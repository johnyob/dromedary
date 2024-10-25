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

type t = (String.t, Constraint.variable, String.comparator_witness) Map.t

let empty = Map.empty (module String)

let find_var t var =
  Result.of_option (Map.find t var) ~error:(`Unbound_type_variable var)


let add t var cvar = Map.set t ~key:var ~data:cvar

let of_alist alist =
  match Map.of_alist (module String) alist with
  | `Ok t -> Ok t
  | `Duplicate_key key -> Error (`Duplicate_type_variable key)


let to_alist t = Map.to_alist t
let of_map t = t
let to_map t = t
let dom t = Map.keys t
let rng t = to_alist t |> List.map ~f:snd
let merge t1 t2 = Map.merge_skewed t1 t2 ~combine:(fun ~key:_ _ a -> a)
