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

(** [t] represents the typing environment Ω. *)
type t

val empty : t

val add_type_decl : t -> type_declaration -> t

(** [find_constr t constr] returns the constructor declaration w/ constructor name [constr]. *)
val find_constr
  :  t
  -> string
  -> (constructor_declaration, [> `Unbound_constructor of string ]) Result.t

(** [find_label t label] returns the label declaration w/ label name [label]. *)
val find_label
  :  t
  -> string
  -> (label_declaration, [> `Unbound_label of string ]) Result.t
