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
open Constraint

type t =
  { existential_bindings : Shallow_type.binding list
  ; gamma : (String.t, variable, String.comparator_witness) Map.t
  }

let empty = { existential_bindings = []; gamma = Map.empty (module String) }

let merge t1 t2 =
  let exception Non_linear_pattern of string in
  try
    Ok
      { existential_bindings = t1.existential_bindings @ t2.existential_bindings
      ; gamma =
          Map.merge_skewed t1.gamma t2.gamma ~combine:(fun ~key _ _ ->
              raise (Non_linear_pattern key))
      }
  with
  | Non_linear_pattern term_var -> Error (`Non_linear_pattern term_var)


let of_existential_bindings bindings =
  { existential_bindings = bindings; gamma = Map.empty (module String) }


let of_binding (x, a) =
  { existential_bindings = []; gamma = Map.singleton (module String) x a }


let to_bindings t = Map.to_alist t.gamma |> List.map ~f:(fun (x, a) -> x #= a)
let to_existential_bindings t = t.existential_bindings