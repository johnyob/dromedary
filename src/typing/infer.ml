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

(* open Misc
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

  type 'a map = (String.t, 'a, String.comparator_witness) Map.t

  type t =
    { types : type_declaration map
    ; constrs : constructor_description map
    ; labels : label_description map
    ; vars : variable map
    }

  (* TODO: Find, etc *)
end

(* ------------------------------------------------------------------------- *)

(* Type former combinators *)

let ( @-> ) x y = Type.form (Type_former.Ttyp_form_arrow (x, y))
let tuple ts = Type.form (Type_former.Ttyp_form_tuple ts)
let constr ts constr = Type.form (Type_former.Ttyp_form_constr (ts, constr))
let int = Type.form (Type_former.Ttyp_form_constr ([], "int"))
let bool = Type.form (Type_former.Ttyp_form_constr ([], "bool"))
let unit = Type.form (Type_former.Ttyp_form_constr ([], "unit"))

(* ------------------------------------------------------------------------- *)

(* Constraint generation and inference *)

(* We first open the relevant syntax modules. *)

open Ast_types
open Parsetree
open Typedtree

(* ------------------------------------------------------------------------- *)

(* Constants and primitives *)

let infer_constant const =
  match const with
  | Const_int _ -> int
  | Const_bool _ -> bool
  | Const_unit -> unit


let infer_primitive prim =
  match prim with
  | Prim_add | Prim_sub | Prim_div | Prim_mul -> int @-> int @-> int


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

  let to_bindings t = Map.to_alist t
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
    : (Fragment.t * Typedtree.pattern Constraint.t, 'a) Continuation.t
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
      let%map.C () = pat_type =~ tuple (List.map vars ~f:Type.var)
      and pats = C.all pats in
      Tpat_tuple pats
    | Ppat_construct (constr, None) ->
      let%map constr_desc, arg_pat_type =
        lift (infer_constructor env constr pat_type)
      in
      (match arg_pat_type with
      | Some _ -> assert false
      | None ->
        let%map.C constr_desc = constr_desc in
        Tpat_construct (constr_desc, None))
    | Ppat_construct (constr, Some arg_pat) ->
      let%bind constr_desc, arg_pat_type =
        lift (infer_constructor env constr pat_type)
      in
      (match arg_pat_type with
      | None -> assert false
      | Some arg_pat_type ->
        let%map arg_pat = infer_pat arg_pat arg_pat_type in
        let%map.C constr_desc = constr_desc
        and arg_pat = arg_pat in
        Tpat_construct (constr_desc, Some arg_pat))
    | Ppat_constraint (pat, pat_type') ->
      let pat_type' = convert_core_type env pat_type' in
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
  Pattern_monad.run (infer_pat pat pat_type)


(* ------------------------------------------------------------------------- *)

(* Expressions *)

let infer_exp env exp exp_type =
  let open Continuation in
  let open Let_syntax in
  let module C = Constraint in
  let rec infer_exp exp exp_type
      : (Typedtree.expression Constraint.t, 'a) Continuation.t
    =
    let%map exp_desc = infer_exp_desc exp exp_type in
    let%map.C exp_desc = exp_desc
    and exp_type = decode exp_type in
    { exp_desc; exp_type }
  and infer_exp_desc exp exp_type
      : (Typedtree.expression_desc Constraint.t, 'a) Continuation.t
    =
    match exp with
    | Pexp_var x ->
      return
        (let%map.C instances = inst x exp_type in
         Texp_var (x, instances))
    | Pexp_prim prim ->
      return
        (let%map.C () = exp_type =~ infer_primitive prim in
         Texp_prim prim)
    | Pexp_const const ->
      return
        (let%map.C () = exp_type =~ infer_constant const in
         Texp_const const)
    | Pexp_fun (pat, exp) ->
      let%bind [ var1; var2 ] =
        exists Size.two >>| Sized_list.map ~f:Type.var
      in
      let%map fragment, pat = infer_pat env pat var1
      and exp = infer_exp exp var2 in
      let%map.C () = exp_type =~ var1 @-> var2
      and pat = pat
      and exp = def (Fragment.to_bindings fragment) exp in
      Texp_fun (pat, exp)
    | Pexp_app (exp1, exp2) ->
      let%bind var = exists Size.one >>| fun [ v ] -> Type.var v in
      let%map exp1 = infer_exp exp1 (var @-> exp_type)
      and exp2 = infer_exp exp2 var in
      let%map.C exp1 = exp1
      and exp2 = exp2 in
      Texp_app (exp1, exp2)
    | Pexp_constraint (exp, exp_type') ->
      let exp_type' = convert_core_type env exp_type' in
      let%map exp_desc = infer_exp_desc exp exp_type' in
      let%map.C () = exp_type =~ exp_type'
      and exp_desc = exp_desc in
      exp_desc
    | Pexp_construct (constr, None) ->
      let%map constr_desc, arg_exp_type =
        infer_constructor env constr exp_type
      in
      (match arg_exp_type with
      | Some _ -> assert false
      | None ->
        let%map.C constr_desc = constr_desc in
        Texp_construct (constr_desc, None))
    | Pexp_construct (constr, Some arg_exp) ->
      let%bind constr_desc, arg_exp_type =
        infer_constructor env constr exp_type
      in
      (match arg_exp_type with
      | None -> assert false
      | Some arg_exp_type ->
        let%map arg_exp = infer_exp arg_exp arg_exp_type in
        let%map.C constr_desc = constr_desc
        and arg_exp = arg_exp in
        Texp_construct (constr_desc, Some arg_exp))
    | Pexp_tuple exps ->
      let%map vars, exps = infer_exps exps in
      let%map.C () = exp_type =~ tuple (List.map vars ~f:Type.var)
      and exps = C.all exps in
      Texp_tuple exps
    | Pexp_match (match_exp, cases) ->
      let%bind var = exists Size.one >>| fun [ v ] -> Type.var v in
      let%map match_exp = infer_exp match_exp var
      and cases = infer_cases cases var exp_type in
      let%map.C match_exp = match_exp
      and match_exp_type = decode var
      and cases = cases in
      Texp_match (match_exp, match_exp_type, cases)
    | Pexp_ifthenelse (if_exp, then_exp, else_exp) ->
      let%map if_exp = infer_exp if_exp bool
      and then_exp = infer_exp then_exp exp_type
      and else_exp = infer_exp else_exp exp_type in
      let%map.C if_exp = if_exp
      and then_exp = then_exp
      and else_exp = else_exp in
      Texp_ifthenelse (if_exp, then_exp, else_exp)
    | _ -> assert false
  and infer_exps exps =
    List.fold_left
      exps
      ~init:(return ([], []))
      ~f:(fun accum exp ->
        let%bind [ var ] = exists Size.one in
        let%map exp = infer_exp exp (Type.var var)
        and vars, exps = accum in
        var :: vars, exp :: exps)
  and infer_cases cases lhs_type rhs_type =
    List.map cases ~f:(fun { pc_lhs; pc_rhs } ->
        let%map fragment, pat = infer_pat env pc_lhs lhs_type
        and exp = infer_exp pc_rhs rhs_type in
        let%map.C tc_lhs = pat
        and tc_rhs = def (Fragment.to_bindings fragment) exp in
        { tc_lhs; tc_rhs })
    |> Continuation.all
  in
  Continuation.run (infer_exp exp exp_type) (fun x -> x) *)
