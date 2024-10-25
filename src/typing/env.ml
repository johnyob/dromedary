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
open Types
open Typedtree
open Constraint

type t =
  { constrs : constructor_declaration map
  ; labels : label_declaration map
  ; abbrevs : Constraint.Abbreviations.t
  }

and 'a map = (String.t, 'a, String.comparator_witness) Map.t

let empty =
  let empty_map () = Map.empty (module String) in
  { constrs = empty_map ()
  ; labels = empty_map ()
  ; abbrevs = Constraint.Abbreviations.empty
  }


let add_label_decl t (label_decl : label_declaration) =
  { t with
    labels = Map.set t.labels ~key:label_decl.label_name ~data:label_decl
  }


let add_constr_decl t (constr_decl : constructor_declaration) =
  { t with
    constrs =
      Map.set t.constrs ~key:constr_decl.constructor_name ~data:constr_decl
  }


let convert_alias { alias_alphas; alias_name; alias_type } =
  let open Algebra.Type_former in
  let substitution_alist =
    List.map alias_alphas ~f:(fun x -> x, Abbrev_type.make_var ())
  in
  let substitution = Type_var.Map.of_alist_exn substitution_alist in
  let alias_former = Constr (List.map ~f:snd substitution_alist, alias_name) in
  let rec convert type_expr =
    match Type_expr.desc type_expr with
    | Ttyp_var var -> Map.find_exn substitution var
    | Ttyp_arrow (t1, t2) ->
      Abbrev_type.make_former (Arrow (convert t1, convert t2))
    | Ttyp_tuple ts -> Abbrev_type.make_former (Tuple (List.map ts ~f:convert))
    | Ttyp_constr (ts, constr_name) ->
      Abbrev_type.make_former (Constr (List.map ts ~f:convert, constr_name))
    | Ttyp_variant _ | Ttyp_row_cons _ | Ttyp_row_uniform _ ->
      raise_s
        [%message "Unsupported alias type expression" (type_expr : type_expr)]
  in
  alias_former, convert alias_type


let add_type_decl t type_decl =
  match type_decl.type_kind with
  | Type_record label_decls ->
    List.fold_left label_decls ~init:t ~f:(fun t label_decl ->
      add_label_decl t label_decl)
  | Type_variant constr_decls ->
    List.fold_left constr_decls ~init:t ~f:(fun t constr_decl ->
      add_constr_decl t constr_decl)
  | Type_alias alias ->
    let abbrev = convert_alias alias in
    { t with abbrevs = Constraint.Abbreviations.add t.abbrevs ~abbrev }
  | Type_abstract | Type_open -> t


let add_ext_constr t ext_constr =
  let { text_kind = Text_decl constr_decl; _ } = ext_constr in
  add_constr_decl t constr_decl


let add_type_ext t type_ext =
  List.fold_left type_ext.tyext_constructors ~init:t ~f:add_ext_constr


let to_abbrevs t = t.abbrevs

let find_constr env constr =
  Map.find env.constrs constr |> Result.of_option ~error:`Unbound_constructor


let find_label env label =
  Map.find env.labels label |> Result.of_option ~error:`Unbound_label
