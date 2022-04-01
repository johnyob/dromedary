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

open! Import
open Predefined
open Constraint

(* [core_type core_type] converts core type [core_type] to [Type.t]. *)
let rec core_type ~substitution t =
  let open Parsetree in
  let open Result in
  let open Let_syntax in
  match t with
  | Ptyp_var x -> Substitution.find_var substitution x >>| Type.var
  | Ptyp_arrow (t1, t2) ->
    let%bind t1 = core_type ~substitution t1 in
    let%bind t2 = core_type ~substitution t2 in
    return (t1 @-> t2)
  | Ptyp_tuple ts ->
    let%bind ts = List.map ts ~f:(core_type ~substitution) |> all in
    return (tuple ts)
  | Ptyp_constr (ts, constr') ->
    let%bind ts = List.map ts ~f:(core_type ~substitution) |> all in
    return (constr ts constr')
  | Ptyp_variant t ->
    let%bind t = row ~substitution t in
    return (variant t)
  | Ptyp_row_cons (tag, t1, t2) ->
    let%bind t1 = core_type ~substitution t1 in
    let%bind t2 = row ~substitution t2 in
    return (row_cons tag (present t1) t2)
  | Ptyp_row_empty -> return (row_uniform absent)


and row ~substitution = core_type ~substitution

(* [type_expr type_expr] converts type expression [type_expr] to [Type.t]. *)
let rec type_expr ~substitution t =
  let open Types in
  let open Result in
  let open Let_syntax in
  match type_desc t with
  | Ttyp_var x -> Substitution.find_var substitution x >>| Type.var
  | Ttyp_arrow (t1, t2) ->
    let%bind t1 = type_expr ~substitution t1 in
    let%bind t2 = type_expr ~substitution t2 in
    return (t1 @-> t2)
  | Ttyp_tuple ts ->
    let%bind ts = List.map ts ~f:(type_expr ~substitution) |> all in
    return (tuple ts)
  | Ttyp_constr (ts, constr') ->
    let%bind ts = List.map ts ~f:(type_expr ~substitution) |> all in
    return (constr ts constr')
  | Ttyp_alias _ -> fail (`Type_expr_contains_alias t)
  | Ttyp_variant t ->
    let%bind t = type_expr_row ~substitution t in
    return (variant t)
  | _ -> fail (`Type_expr_is_ill_sorted t)


and type_expr_row ~substitution t =
  let open Types in
  let open Result in
  let open Let_syntax in
  match type_desc t with
  | Ttyp_row_cons (label, t1, t2) ->
    let%bind t1 = type_expr ~substitution t1 in
    let%bind t2 = type_expr_row ~substitution t2 in
    return (row_cons label t1 t2)
  | Ttyp_row_uniform t ->
    let%bind t = type_expr ~substitution t in
    return (row_uniform t)
  | _ -> fail (`Type_expr_is_ill_sorted t)


module With_computation (Computation : Computation.S) = struct
  let with_computation ~f ~message t =
    let open Computation in
    let open Let_syntax in
    let%bind substitution = substitution in
    of_result (f ~substitution t) ~message


  let core_type =
    with_computation ~f:core_type ~message:(fun (`Unbound_type_variable var) ->
        [%message
          "Unbound type variable when converting core type" (var : string)])


  let row =
    with_computation ~f:row ~message:(fun (`Unbound_type_variable var) ->
        [%message "Unbound type variable when converting row" (var : string)])


  let type_expr =
    let open Types in
    with_computation ~f:type_expr ~message:(function
        | `Unbound_type_variable var ->
          [%message
            "Unbound type variable when converting type expression"
              (var : string)]
        | `Type_expr_is_ill_sorted type_expr ->
          [%message "Type expression is ill-sorted" (type_expr : type_expr)]
        | `Type_expr_contains_alias type_expr ->
          [%message "Type expression contains alias" (type_expr : type_expr)])
end
