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

(* [core_type core_type] converts core type [core_type] to [Type.t],
   generating row variables where applicable *)
let rec core_type ~substitution t =
  let open Parsetree in
  let open Result in
  let open Let_syntax in
  match t with
  | Ptyp_var x ->
    let%bind x = Substitution.find_var substitution x in
    return ([], Type.var x)
  | Ptyp_arrow (t1, t2) ->
    let%bind vars1, t1 = core_type ~substitution t1 in
    let%bind vars2, t2 = core_type ~substitution t2 in
    return (vars1 @ vars2, t1 @-> t2)
  | Ptyp_tuple ts ->
    let%bind var_ts = List.map ts ~f:(core_type ~substitution) |> all in
    let vars, ts = List.unzip var_ts in
    return (List.concat vars, tuple ts)
  | Ptyp_constr (ts, constr') ->
    let%bind var_ts = List.map ts ~f:(core_type ~substitution) |> all in
    let vars, ts = List.unzip var_ts in
    return (List.concat vars, constr ts constr')
  | Ptyp_variant t ->
    let%bind vars, t = row ~substitution t in
    return (vars, variant t)
  | Ptyp_mu (x, t) ->
    let x' = fresh () in
    let%bind vars, t = core_type ~substitution:(Substitution.add substitution x x') t in
    return (vars, Type.mu x' t)
  | Ptyp_where (t1, x, t2) ->
    let x' = fresh () in
    let%bind vars1, t2 = core_type ~substitution t2 in
    let%bind vars2, t1 = core_type ~substitution:(Substitution.add substitution x x') t1 in
    return (vars1 @ vars2, Type.let_ ~binding:(x', t2) ~in_:t1)


and row ~substitution (row_fields, closed_flag) =
  let open Result.Let_syntax in
  let vars, tl =
    match closed_flag with
    | Closed -> [], row_uniform absent
    | Open ->
      let var = fresh () in
      [ var ], Type.var var
  in
  let%bind vars, row =
    List.fold_right row_fields ~init:(return (vars, tl)) ~f:(fun rf tl ->
        let%bind vars1, tl = tl in
        let%bind vars2, row = row_field ~substitution rf tl in
        return (vars1 @ vars2, row))
  in
  return (vars, row)


and row_field ~substitution (Row_tag (tag, t)) tl = 
  let open Result.Let_syntax in
  let%bind vars, t = 
    match t with
    | None -> return ([], present unit)
    | Some t ->
      let%bind vars, t = core_type ~substitution t in
      return (vars, present t)
  in
  return (vars, row_cons tag t tl)



(* [type_expr type_expr] converts type expression [type_expr] to [Type.t]. *)
let rec type_expr ~substitution t =
  let open Types in
  let open Result in
  let open Let_syntax in
  match Type_expr.desc t with
  | Ttyp_var var ->
    Type_var.Map.find substitution var
    |> Result.of_option ~error:(`Unbound_type_variable var)
    >>| Type.var
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
  | Ttyp_variant t ->
    let%bind t = type_expr_row ~substitution t in
    return (variant t)
  | _ -> fail (`Type_expr_is_ill_sorted t)


and type_expr_row ~substitution t =
  let open Types in
  let open Result in
  let open Let_syntax in
  match Type_expr.desc t with
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


  let type_expr ~substitution t =
    let open Types in
    Computation.of_result (type_expr ~substitution t) ~message:(function
        | `Unbound_type_variable var ->
          [%message
            "Unbound type variable when converting type expression"
              (var : type_var)]
        | `Type_expr_is_ill_sorted type_expr ->
          [%message "Type expression is ill-sorted" (type_expr : type_expr)]
        | `Type_expr_contains_alias type_expr ->
          [%message "Type expression contains alias" (type_expr : type_expr)])
end
