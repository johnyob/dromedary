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

type t

val empty : t

val find_var
  :  t
  -> var:string
  -> (Constraint.variable, [> `Unbound_type_variable of string ]) Result.t

val of_alist
  :  (string * Constraint.variable) list
  -> (t, [> `Duplicate_type_variable of string ]) Result.t

val to_alist : t -> (string * Constraint.variable) list

val of_type_vars
  :  string list
  -> (t, [> `Duplicate_type_variable of string ]) Result.t

val type_vars : t -> string list
val constraint_vars : t -> Constraint.variable list
val compose : t -> t -> t