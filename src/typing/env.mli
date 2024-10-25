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
open Types
open Typedtree

(** [t] represents the typing environment Ω. *)
type t

val empty : t
val add_type_decl : t -> type_declaration -> t
val add_ext_constr : t -> extension_constructor -> t
val add_type_ext : t -> type_extension -> t
val to_abbrevs : t -> Abbreviations.t

(** [find_constr t constr] returns the constructor declaration w/ constructor name [constr]. *)
val find_constr
  :  t
  -> string
  -> (constructor_declaration, [> `Unbound_constructor ]) Result.t

(** [find_label t label] returns the label declaration w/ label name [label]. *)
val find_label
  :  t
  -> string
  -> (label_declaration, [> `Unbound_label ]) Result.t
