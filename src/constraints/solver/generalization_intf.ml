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

(* This module implements the interfaces for generalization. *)

open! Import

module type S = sig
  (** Abstract types to be substituted by functor arguments. *)

  (** The type ['a former] is the type formers (with children of type ['a]), 
      given by the functor argument [Former]. *)

  type 'a former

  (** Generalization requires additional metadata stored in "tag". *)

  module Tag : sig
    type t [@@deriving sexp_of]
  end

  module Abbreviations :
    Abbreviations.S with type 'a former := 'a former and type metadata := Tag.t

  module Unifier = Abbreviations.Unifier

  (** The type [scheme] defines the abstract notion of a scheme in 
      "graphic" types.
      
      A scheme has a notion of "bound" variables, this is encoded in the
      type [variables]. 
      
      We note that all bound variables to a *generalized* scheme
      are *rigid*. 
  *)

  type scheme

  (** The notion of "bound" variables for a scheme is shared between
      instantiation and computing the set of generic variables,
      given a scheme. 
  *)

  type variables = Unifier.Type.t list

  (** [root scheme] returns the root node, or quantifier "body" of the
      scheme [scheme]. *)
  val root : scheme -> Unifier.Type.t

  (** [variables scheme] computes the bound variables of a scheme [scheme]. *)
  val variables : scheme -> variables

  (** [mono_scheme] creates a scheme with no generic variables. *)
  val mono_scheme : Unifier.Type.t -> scheme

  (** The generalization module maintains several bits of mutable
      state related to it's implemented of efficient level-based
      generalization.
    
      We encapsulate this in the abstract type [state].  
  *)

  type state

  (** [make_state ()] creates a new empty state. *)
  val make_state : Abbreviations.Ctx.t -> state

  (** [enter state] creates a new "stack frame" in the constraint solver
     and enters it.  *)

  val enter : state -> unit

  (** [make_flexible_var] creates a fresh unification variable. *)

  val make_flexible_var : state -> Unifier.Type.t

  (** [make_rigid_var] creates a fresh rigid variable. *)
  val make_rigid_var : state -> Unifier.Rigid_var.t -> Unifier.Type.t

  (** [make_former] creates a fresh unification type node 
      w/ the structure provided by the former. *)

  val make_former : state -> Unifier.Type.t former -> Unifier.Type.t
  val unify : state -> Unifier.Type.t -> Unifier.Type.t -> unit

  (** [instantiate scheme] instantates the scheme [scheme]. It does so, by
      taking fresh copies of the generic variables, without necessarily
      copying other bits of the type. 
      
      This is designed for efficient sharing of nodes within the
      "graphic type". 
  *)
  val instantiate : state -> scheme -> variables * Unifier.Type.t

  exception Rigid_variable_escape of Unifier.Rigid_var.t
  exception Cannot_flexize of Unifier.Rigid_var.t

  val exit
    :  state
    -> rigid_vars:Unifier.Rigid_var.t list
    -> types:Unifier.Type.t list
    -> variables * scheme list

  (** [fold_acyclic type_ ~var ~former] will perform a bottom-up fold
      over the (assumed) acyclic graph defined by the type [type_].  
  *)

  val fold_acyclic
    :  Unifier.Type.t
    -> flexible_var:(Unifier.Type.t -> 'a)
    -> rigid_var:(Unifier.Rigid_var.t -> Unifier.Type.t -> 'a)
    -> former:('a former -> 'a)
    -> 'a

  (** [fold_cyclic type_ ~var ~former ~mu] will perform a fold over
      the (potentially) cyclic graph defined by the type [type_].  
  *)

  val fold_cyclic
    :  Unifier.Type.t
    -> flexible_var:(Unifier.Type.t -> 'a)
    -> rigid_var:(Unifier.Rigid_var.t -> Unifier.Type.t -> 'a)
    -> former:('a former -> 'a)
    -> mu:(Unifier.Type.t -> 'a -> 'a)
    -> 'a
end

(** The interface of {generalization.ml}. *)

module type Intf = sig
  module type S = S

  (** The functor [Make]. *)
  module Make (Former : Type_former.S) : S with type 'a former := 'a Former.t
end
