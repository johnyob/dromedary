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

(* This module implements the interfaces for equations and their context. *)

open! Import

module type S = sig
  (** Abstract types to be substituted by functor arguments. *)

  (** The type ['a former] is the type formers (with children of type ['a]), 
      given by the functor argument [Former]. *)

  type 'a former

  (** [metadata] is the type of metadata, given by the functor argument
      [Metadata]. *)
  type metadata

  (** [rigid_metadata] is the type of metadata, given by the functor argument
      [Rigid_metadata]. *)
  type rigid_metadata

  (** Ambivalent types

      A rigid type is a type that namely consists of rigid variables and type formers:
        ɳ ::= a | (ɳ, ..., ɳ) F
     
      Rigid types form part of the equational context E:
        E ::= . | E, ɳ = ɳ

      An ambivalent type φ is defined by:
        φ ::= τ = a₁ = ... = aₙ

      An ambivalent type φ is consistent wrt to E if E ||- τ = a₁ = ... = aₙ. 
  *)

  (** [state] represents the globally persistent state used to model equational contexts. *)
  type state

  val make_state : unit -> state

  module Rigid_type : sig
    (** [t] represents a rigid type (in graphical form), as defined above. *)
    type t [@@deriving sexp_of]

    type structure =
      | Var
      | Former of t former

    val id : state -> t -> state * int
    val get_structure : state -> t -> state * structure
    val set_structure : state -> t -> structure -> state
    val get_metadata : state -> t -> state * rigid_metadata
    val set_metadata : state -> t -> rigid_metadata -> state
  end

  val make_rigid_var : state -> rigid_metadata -> state * Rigid_type.t

  val make_rigid_former
    :  state
    -> Rigid_type.t former
    -> rigid_metadata
    -> state * Rigid_type.t

  module Ambivalence : sig
    type t = Rigid_type.t list [@@deriving sexp_of]
  end

  module Unifier :
    Unifier.S
      with type 'a former := 'a former
       and type metadata := Ambivalence.t * metadata

  (** An equation [t : Equation.t] denotes some arbitrary equality. *)
  module Equation : sig
    type t [@@deriving sexp_of]

    (** [type1 =. type2] returns an equation that encodes the equality 
        between [type1] and [type2]. *)
    val ( =. ) : Rigid_type.t -> Rigid_type.t -> t
  end

  exception Inconsistent

  (** [add_equation t equation] adds the equation [equation] to [t]. 
      [Inconsistent] is raised if we can deduce false from the context [t; equation]. 
  *)
  val add_equation : state -> Equation.t -> state

  (** [consistency_check t types] determines whether types [types] are consistent under the 
      context [t]. *)
  val consistency_check : state -> Unifier.Type.t list -> state * bool
end

(** The interface of {equations.ml}. *)

module type Intf = sig
  module type S = S

  (** The functor [Make]. *)
  module Make
      (Former : Type_former.S)
      (Metadata : Unifier.Metadata)
      (Rigid_metadata : Unifier.Metadata) :
    S
      with type 'a former := 'a Former.t
       and type metadata := Metadata.t
       and type rigid_metadata := Rigid_metadata.t
end