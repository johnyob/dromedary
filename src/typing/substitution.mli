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

(** A substitution θ is a mapping from type variables to constraint variables.
    
    During inference, a computation ['a Computation.t] must keep track of
    a local substitution between explicitly bound type variables and their
    generated constraint variables. 
*)

(** type [t] encodes a substitution θ. *)
type t

(** [empty] is the empty substitution, mapping no variables. *)
val empty : t

(** [find_var t var] returns the mapped constraint variable of type variable [var]. *)
val find_var
  :  t
  -> string
  -> (Constraint.variable, [> `Unbound_type_variable of string ]) Result.t

(** [of_alist alist] returns the substitution defined by the associative list [alist]. *)
val of_alist
  :  (string * Constraint.variable) list
  -> (t, [> `Duplicate_type_variable of string ]) Result.t

val of_map
  :  (String.t, Constraint.variable, String.comparator_witness) Map.t
  -> t

val to_map
  :  t
  -> (String.t, Constraint.variable, String.comparator_witness) Map.t

(** [to_alist t] returns the alist defined by the substitution [t]. *)
val to_alist : t -> (string * Constraint.variable) list

(** [dom t] returns the domain of [t]. *)
val dom : t -> string list

(** [rng t] returns the range (or image) of [t]. *)
val rng : t -> Constraint.variable list

(** [merge t1 t2] returns the merged substitution of [t1] and [t2]. *)
val merge : t -> t -> t