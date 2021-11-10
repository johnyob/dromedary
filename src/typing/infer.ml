(*****************************************************************************)
(*                                                                           *)
(*                                Dromedary                                  *)
(*                                                                           *)
(*                Alistair O'Brien, University of Cambridge                  *)
(*                                                                           *)
(* Copyright 2021 Alistair O'Brien.                                          *)
(*                                                                           *)
(* All rights reserved. This file is distributed under the terms of the MIT  *)
(* license, as described in the file LICENSE.                                *)
(*                                                                           *)
(*****************************************************************************)

open Misc
open Parsing
open Base

(* ------------------------------------------------------------------------- *)

(* Implement required interfaces from [Constraints.Intf]. *)

module Term_var = struct
  type t = string [@@deriving sexp_of, compare]
end

module Type_var = struct
  type t = string [@@deriving sexp_of]

  let of_int x = "α" ^ Int.to_string x
end

module Type_former = struct
  type 'a t =
    | Ttyp_form_arrow of 'a * 'a
    | Ttyp_form_tuple of 'a list
    | Ttyp_form_constr of 'a list * string
  [@@deriving sexp_of]

  let map t ~f =
    match t with
    | Ttyp_form_arrow (t1, t2) ->
      let t1' = f t1 in
      let t2' = f t2 in
      Ttyp_form_arrow (t1', t2')
    | Ttyp_form_tuple ts -> Ttyp_form_tuple (List.map ~f ts)
    | Ttyp_form_constr (ts, constr) -> Ttyp_form_constr (List.map ~f ts, constr)


  let iter t ~f =
    let (_ : unit t) = map t ~f in
    ()


  let fold t ~f ~init =
    match t with
    | Ttyp_form_arrow (t1, t2) ->
      let init = f t1 init in
      let init = f t2 init in
      init
    | Ttyp_form_tuple ts -> List.fold_right ~f ~init ts
    | Ttyp_form_constr (ts, _) -> List.fold_right ~f ~init ts


  exception Iter2

  let iter2 t1 t2 ~f =
    let list_iter2 xs ys ~f =
      (* Catch the [Base] exception and re-raise our exception *)
      try List.iter2_exn xs ys ~f with
      | _ -> raise Iter2
    in
    match t1, t2 with
    | Ttyp_form_arrow (t11, t12), Ttyp_form_arrow (t21, t22) ->
      f t11 t21;
      f t12 t22
    | Ttyp_form_tuple ts1, Ttyp_form_tuple ts2 -> list_iter2 ts1 ts2 ~f
    | Ttyp_form_constr (ts1, constr1), Ttyp_form_constr (ts2, constr2)
      when String.equal constr1 constr2 -> list_iter2 ts1 ts2 ~f
    | _, _ -> raise Iter2
end

module Type = struct
  type var = Type_var.t
  type 'a former = 'a Type_former.t
  type t = Types.type_expr [@@deriving sexp_of]

  open Types

  let var x = Ttyp_var x

  let form former =
    let open Type_former in
    match former with
    | Ttyp_form_arrow (t1, t2) -> Ttyp_arrow (t1, t2)
    | Ttyp_form_tuple ts -> Ttyp_tuple ts
    | Ttyp_form_constr (ts, constr) -> Ttyp_constr (ts, constr)
end

module T = struct
  module Var = Type_var
  module Former = Type_former
  module Type = Type

  type scheme = Var.t list * Type.t
end

(* ------------------------------------------------------------------------- *)

(* Instantiate constraints and solver *)

module Constraint = Constraints.Constraint.Make (Term_var) (T)
module Solver = Constraints.Solver.Make (Term_var) (T)
open Constraint
open Solver

(* ------------------------------------------------------------------------- *)

(* Environment for datatypes, constructors and labels. *)

module Env = struct
  open Types

  type 'a map = string

  type t =
    { types : type_declaration map
    ; constrs : constructor_description map
    ; labels : label_description map
    }

  (* TODO: Find, etc *)
end

(* ------------------------------------------------------------------------- *)

(* Type former combinators *)

let ( @-> ) x y = Type_former.Ttyp_form_arrow (x, y)
let tuple ts = Type.Form (Type_former.Ttyp_form_tuple ts)
let constr ts string = Type_former.Ttyp_form_constr (ts, string)

(* ------------------------------------------------------------------------- *)

(* Constraint generation and inference *)

(* We first open the relevant syntax modules. *)

open Parsetree
open Typedtree

(* ------------------------------------------------------------------------- *)

(* Patterns *)

module Fragment = struct
  exception Non_linear_pattern of string

  type t = (String.t, Type.t, String.comparator_witness) Map.t

  let empty = Map.empty (module String)
  let singleton x typ = Map.singleton (module String) x typ

  let extend t x typ =
    try Map.add_exn t ~key:x ~data:typ with
    | _ -> raise (Non_linear_pattern x)


  let merge t1 t2 =
    Map.merge_skewed t1 t2 ~combine:(fun ~key _ _ ->
        raise (Non_linear_pattern key))
end

let infer_pat env pat typ
    : (Fragment.t * Typedtree.pattern Constraint.t, 'a) Continuation.t
  =
  (* Infer pattern is split into 2 mutually recursive functions, infering the
     pattern and inferring the pattern_desc *)
  let module Cst = Constraint in
  let module Cnt = Continuation in
  let rec infer_pat pat typ
      : (Fragment.t * Typedtree.pattern Constraint.t, 'a) Continuation.t
    =
    let open Cnt.Let_syntax in
    let%bind fragment, pat_desc = infer_pat_desc pat typ in
    return
      ( fragment
      , let%map.Cst pat_desc = pat_desc
        and pat_type = decode typ in
        { pat_desc; pat_type } )
  and infer_pat_desc pat typ
      : (Fragment.t * Typedtree.pattern_desc Constraint.t, 'a) Continuation.t
    =
    let open Cnt.Let_syntax in
    match pat with
    | Ppat_any -> return (Fragment.empty, Cst.return Tpat_any)
    | Ppat_var x -> return (Fragment.singleton x typ, Cst.return (Tpat_var x))
    | Ppat_alias (pat, x) ->
      let%bind fragment, pat = infer_pat pat typ in
      return
        ( Fragment.extend fragment x typ
        , let%map.Cst pat = pat in
          Tpat_alias (pat, x) )
    | Ppat_constant constant ->
      return
        ( Fragment.empty
        , let%map.Cst () = typ =~ infer_constant constant in
          Tpat_constant constant )
    | Ppat_tuple pats ->
      let%bind fragment, vars, pats =
        List.fold_left
          pats
          ~init:(return (Fragment.empty, [], []))
          ~f:(fun accum pat ->
            let%bind [ var ] = exists Size.one
            and fragment1, pat = infer_pat pat (Type.Var var)
            and fragment2, vars, pats = accum in
            return (Fragment.merge fragment1 fragment2, var :: vars, pat :: pats))
      in
      return
        ( fragment
        , let%map.Cst () =
            typ =~ tuple (List.map vars ~f:(fun var -> Type.Var var))
          and pats = Cst.all pats in
          Tpat_tuple pats )
    | Ppat_construct (constr, arg_pat) ->
      let%bind constr_desc, arg_pat_typ = infer_constructor env constr typ in
      let%bind fragment, arg_pat =
        match arg_pat, arg_pat_typ with
        | None, None -> return (Fragment.empty, Cst.return None)
        | Some arg_pat, Some arg_pat_typ ->
          infer_pat arg_pat arg_pat_typ
          >>| fun (fragment, cst) -> fragment, Cst.map cst ~f:Option.some
        | _, _ -> assert false
      in
      return
        ( fragment
        , let%map.Cst constr_desc = constr_desc
          and arg_pat = arg_pat in
          Tpat_construct (constr_desc, arg_pat) )
    | Ppat_constraint (pat, typ') ->
      let%bind typ' = convert_typ typ' in
      let%bind fragment, pat = infer_pat pat typ' in
      return
        ( fragment
        , let%map.Cst () = typ =~ typ'
          and pat = pat in
          pat.pat_desc )
    | Ppat_record _ -> failwith "Implement later"
  in
  infer_pat pat typ
