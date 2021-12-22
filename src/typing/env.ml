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

open Base
open Types

type t =
  { types : type_declaration map
  ; constrs : constructor_declaration map
  ; labels : label_declaration map
  }

and 'a map = (String.t, 'a, String.comparator_witness) Map.t

let empty =
  let empty_map () = Map.empty (module String) in
  { types = empty_map (); constrs = empty_map (); labels = empty_map () }


let add_label_decl t (label_decl : label_declaration) =
  { t with
    labels = Map.set t.labels ~key:label_decl.label_name ~data:label_decl
  }


let add_constr_decl t (constr_decl : constructor_declaration) =
  { t with
    constrs =
      Map.set t.constrs ~key:constr_decl.constructor_name ~data:constr_decl
  }


let add_type_decl t type_decl =
  let t =
    match type_decl.type_kind with
    | Type_record label_decls ->
      List.fold_left label_decls ~init:t ~f:(fun t label_decl ->
          [%test_eq: string list]
            label_decl.label_type_params
            type_decl.type_params;
          add_label_decl t label_decl)
    | Type_variant constr_decls ->
      List.fold_left constr_decls ~init:t ~f:(fun t constr_decl ->
          [%test_eq: string list]
            constr_decl.constructor_type_params
            type_decl.type_params;
          add_constr_decl t constr_decl)
  in
  { t with types = Map.set t.types ~key:type_decl.type_name ~data:type_decl }


let find_constr env constr =
  Map.find env.constrs constr
  |> Result.of_option ~error:(`Unbound_constructor constr)


let find_label env label =
  Map.find env.labels label |> Result.of_option ~error:(`Unbound_label label)
