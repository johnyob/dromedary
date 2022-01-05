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

type flexibility = Rigid | Flexible

type t = (String.t, Constraint.variable * flexibility, String.comparator_witness) Map.t

let empty = Map.empty (module String)

let find_var t var =
  Result.(of_option (Map.find t var) ~error:(`Unbound_type_variable var) >>| fst)

let flexibility_of t var = 
  Result.(of_option (Map.find t var) ~error:(`Unbound_type_variable var) >>| snd)


let of_alist alist =
  match Map.of_alist (module String) alist with
  | `Ok t -> Ok t
  | `Duplicate_key key -> Error (`Duplicate_type_variable key)


let to_alist t = Map.to_alist t
(* 
let of_type_vars vars =
  of_alist (List.map ~f:(fun var -> var, Constraint.fresh ()) vars) *)


let dom t = Map.keys t
let rng t = to_alist t |> List.map ~f:(fun (_, (x, _)) -> x)
let merge t1 t2 = Map.merge_skewed t1 t2 ~combine:(fun ~key:_ _ a -> a)
