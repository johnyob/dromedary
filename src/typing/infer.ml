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

(* Adding a monoid signature might be nice here? *)

module Fragment = struct
  exception Non_linear_pattern of string

  type t = (String.t, Type.t, String.comparator_witness) Map.t

  let empty = Map.empty (module String)
  let singleton x typ = Map.singleton (module String) x typ

  let extend t x typ =
    try Map.add_exn t ~key:x ~data:typ with
    | _ -> raise (Non_linear_pattern x)


  let merge (t1 : t) (t2 : t) : t =
    Map.merge_skewed t1 t2 ~combine:(fun ~key _ _ ->
        raise (Non_linear_pattern key))
end

(* TODO: Find a library that does this, or write one yourself *)

module Pattern_monad : sig
  type ('a, 'b) t

  (* Monad transformer code: *)

  val lift : ('a, 'b) Continuation.t -> ('a, 'b) t
  val run : ('a, 'b) t -> (Fragment.t * 'a, 'b) Continuation.t

  (* Writer monad code: *)

  val write : Fragment.t -> (unit, 'b) t
  val read : ('a, 'b) t -> (Fragment.t, 'b) t
  val listen : ('a, 'b) t -> (Fragment.t * 'a, 'b) t
  val extend : string -> Type.t -> (unit, 'b) t

  include Monad.S2 with type ('a, 'b) t := ('a, 'b) t
end = struct
  type ('a, 'b) t = (Fragment.t * 'a, 'b) Continuation.t

  open Continuation.Let_syntax

  module Basic = struct
    type nonrec ('a, 'b) t = ('a, 'b) t

    let return x = return (Fragment.empty, x)

    let bind t ~f =
      let%bind fragment1, x = t in
      let%map fragment2, y = f x in
      Fragment.merge fragment1 fragment2, y


    let map = `Custom (fun t ~f -> t >>| fun (fragment, x) -> fragment, f x)
  end

  let write fragment = return (fragment, ())
  let read t = t >>| fun (fragment, _) -> fragment, fragment
  let listen t = t >>| fun (fragment, x) -> fragment, (fragment, x)
  let run t = t
  let lift t = t >>| fun x -> Fragment.empty, x
  let extend x typ = write (Fragment.singleton x typ)

  include Monad.Make2 (Basic)
end

let infer_pat env pat pat_type
    : (Typedtree.pattern Constraint.t, 'a) Pattern_monad.t
  =
  let module C = Constraint in
  let open Pattern_monad in
  let open Let_syntax in
  let rec infer_pat pat pat_type
      : (Typedtree.pattern Constraint.t, 'a) Pattern_monad.t
    =
    let%map pat_desc = infer_pat_desc pat pat_type in
    let%map.C pat_desc = pat_desc
    and pat_type = decode pat_type in
    { pat_desc; pat_type }
  and infer_pat_desc pat pat_type
      : (Typedtree.pattern_desc Constraint.t, 'a) Pattern_monad.t
    =
    match pat with
    | Ppat_any -> return (C.return Tpat_any)
    | Ppat_var x -> return (C.return (Tpat_var x))
    | Ppat_alias (pat, x) ->
      let%bind pat = infer_pat pat pat_type in
      let%map () = extend x pat_type in
      let%map.C pat = pat in
      Tpat_alias (pat, x)
    | Ppat_constant constant ->
      return
        (let%map.C () = pat_type =~ infer_constant constant in
         Tpat_constant constant)
    | Ppat_tuple pats ->
      let%map vars, pats = infer_pats pats in
      let%map.C () = pat_type =~ tuple (List.map vars ~f:(fun v -> Type.Var v))
      and pats = C.all pats in
      Tpat_tuple pats
    | Ppat_construct (constr, None) ->
      let%bind constr_desc, arg_pat_type =
        infer_constructor env constr pat_type
      in
      (match%map arg_pat_type with
      | Some _ -> assert false
      | None ->
        let%map.C constr_desc = constr_desc in
        Tpat_construct (constr_desc, None))
    | Ppat_construct (constr, Some arg_pat) ->
      let%bind constr_desc, arg_pat_type =
        infer_constructor env constr pat_type
      in
      let%map arg_pat = infer_pat arg_pat arg_pat_type in
      let%map.C constr_desc = constr_desc
      and arg_pat = arg_pat in
      Tpat_construct (constr_desc, Some arg_pat)
    | Ppat_constraint (pat, pat_type') ->
      let%bind pat_type' = convert_core_type pat_type' in
      let%map pat_desc = infer_pat_desc pat pat_type' in
      let%map.C () = pat_type =~ pat_type'
      and pat_desc = pat_desc in
      pat_desc

  and infer_pats pats
      : ( variable list * Typedtree.pattern Constraint.t list, 'a )
      Pattern_monad.t
    =
    List.fold_left
      pats
      ~init:(return ([], []))
      ~f:(fun accum pat ->
        let%bind [ var ] = lift (exists Size.one) in
        let%map pat = infer_pat pat (Type.Var var)
        and vars, pats = accum in
        var :: vars, pat :: pats)
  in
  infer_pat pat pat_type

(* ------------------------------------------------------------------------- *)
