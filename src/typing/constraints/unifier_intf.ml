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

(* This module implements signatures used by the unifier. *)

(* Unification consists of solving equations between types. 
   For generalization and efficiency, we use "multi-equations":
     e ::= [] | t = e
   
   A multi-equation is standard iff it contains 1 non-variable member,
   known as the [terminal]. *)

open Intf

(* ------------------------------------------------------------------------- *)

(* For abstract purposes, we wrap all data not related to unification in an 
   abstract "metadata" type. 
    
   A concrete example of this metadata would be the level used in 
   generalization. See {!generalization.mli}. 
    
   This abstraction forms a commutative monoid. *)

module type Metadata = sig
  (* [t] is the abstract type of the metadata associated with each variable. *)

  type t [@@deriving sexp_of]

  (* [merge] is performed when unifying two variables. 
     We assume that [merge] is associative and commutative. *)

  val merge : t -> t -> t
end

(* ------------------------------------------------------------------------- *)

(* This functor describes the signatures of the unifier.  *)

module type S = sig
  (* Abstract types to be substituted by functor arguments. *)

  type 'a former
  type metadata

  (* There are two kinds of variables. A [Flexible] variable can
      be unified with other variables and types. A [Rigid] (in general) 
      cannot be unified. *)

  type variable_kind =
    | Flexible
    | Rigid
  [@@deriving sexp_of, eq]

  (* sexp-able for error reporting and prettying printing. *)

  (* Unification involves [variable]s, which are nodes within 
      a multi-equation. *)

  type variable [@@deriving sexp_of, compare]

  (* Each variable consists of:
      - a unique identifier [id] (used to define a total ordering).
      - a variable kind [kind].
      - a mutable [terminal], which contains the [terminal] of the 
        multi-equation.
      - a mutable piece of [metadata]. 
      
      They are accessed via setters and getters: *)

  val id : variable -> int
  val kind : variable -> variable_kind
  val get_terminal : variable -> variable former option
  val set_terminal : variable -> variable former option -> unit
  val get_metadata : variable -> metadata
  val set_metadata : variable -> metadata -> unit

  (* [hash var] computes the hash of the variable [var]. *)

  val hash : variable -> int

  (* [is_rigid var] returns true if [var] is a rigid variable. *)

  val is_rigid : variable -> bool

  (* [is_flexible var] returns true if [var] is a flexible variable. *)

  val is_flexible : variable -> bool

  (* [fresh kind ~terminal ~data ()] returns a fresh variable with kind [kind],
      terminal [terminal] (optional argument) and data [data]. *)

  val fresh
    :  variable_kind
    -> ?terminal:variable former
    -> metadata:metadata
    -> unit
    -> variable

  (* [unify var1 var2] equates the variables [var1] and [var2], 
      and their associated multi-equations.
      
      Identifiers are merged arbitrarily. 
      Terminal are unified recursively, using [iter2]. 
      Metadata are merged using [Metadata.merge].

      [Unify (var1, var2)] is raised if the two variables cannot
      be unified. This occurs with rigid variables or incompatable
      terminals. 

      No occurs check is implemented (this is separate from 
      unification). See {!occurs_check}. *)

  exception Unify of variable * variable

  val unify : variable -> variable -> unit

  (* [occurs_check var] detects whether there is 
      a cycle in the multi-equation associated with var. 
      
      If a cycle is detected, [Cycle var] is raised. *)

  exception Cycle of variable

  val occurs_check : variable -> unit
end

(* ------------------------------------------------------------------------- *)

(* The interface of {unifier.ml}. *)

module type Intf = sig
  module type Metadata = Metadata
  module type S = S

  (* The functor [Make]. *)
  module Make (Former : Type_former) (Metadata : Metadata) :
    S with type 'a former := 'a Former.t and type metadata := Metadata.t
end