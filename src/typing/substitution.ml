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

type t = 
  { flexible_sub : (String.t, Constraint.variable, String.comparator_witness) Map.t
  ; rigid_sub : (String.t, Constraint.rigid_variable, String.comparator_witness) Map.t
  }

let empty = { flexible_sub = Map.empty (module String); rigid_sub = Map.empty (module String) }

let find_flexible_var t var =
  Result.of_option (Map.find t.flexible_sub var) ~error:(`Unbound_type_variable var)

let find_rigid_var t var = 
  Result.of_option (Map.find t.rigid_sub var) ~error:(`Unbound_type_variable var)

let of_alist flex_alist rigid_alist =
  match Map.of_alist (module String) flex_alist, Map.of_alist (module String) rigid_alist with
  | `Ok flexible_sub, `Ok rigid_sub -> Ok { flexible_sub; rigid_sub }
  | `Duplicate_key key, _ | _, `Duplicate_key key -> Error (`Duplicate_type_variable key)


let to_alist t = Map.to_alist t.flexible_sub, Map.to_alist t.rigid_sub

let flexible_dom t = Map.keys t.flexible_sub
let rigid_dom t = Map.keys t.rigid_sub


let flexible_rng t = to_alist t |> fst |> List.map ~f:snd

let rigid_rng t = to_alist t |> snd |> List.map ~f:snd


let merge t1 t2 = 
  { flexible_sub = Map.merge_skewed t1.flexible_sub t2.flexible_sub ~combine:(fun ~key:_ _ a -> a)
  ; rigid_sub = Map.merge_skewed t1.rigid_sub t2.rigid_sub ~combine:(fun ~key:_ _ a -> a)
  }
