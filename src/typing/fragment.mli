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

(* [t] encodes the notion of a fragment Δ. *)
type t

val empty : t
val merge : t -> t -> (t, [> `Non_linear_pattern of string ]) Result.t
val of_existential_bindings : Shallow_type.binding list -> t
val of_binding : string * variable -> t
val to_existential_bindings : t -> Shallow_type.binding list
val to_bindings : t -> binding list