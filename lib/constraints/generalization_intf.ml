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
open Structure

module type S = sig
  (** Abstract types to be substituted by functor arguments. *)

  (** The type [label] is the type for row labels, given by the functor argument
      [Label]. *)
  type label

  (** The type ['a former] is the type formers (with children of type ['a]),
      given by the functor argument [Former]. *)
  type 'a former

  (** The generalization module maintains several bits of mutable
      state related to it's implemented of efficient level-based
      generalization.

      We encapsulate this in the abstract type [state]. *)
  type state

  (** [make_state ()] creates a new empty state. *)
  val make_state : unit -> state

  module Rigid_type : sig
    (** [t] represents a rigid type *)
    type t [@@deriving sexp_of]

    (** [make_rigid_var rigid_var] returns the rigid type
        representing the variable [rigid_var] *)
    val make_rigid_var : Rigid_var.t -> t

    (** [make_former former] returns the rigid type representing the
        rigid type former [former]. *)
    val make_former : t former -> t
  end

  module Abbrev_type : sig
    (** [t] represents a type used to encode abbreviations. *)
    type t [@@deriving sexp_of, compare]

    (** [make_var ()] returns a new type variable *)
    val make_var : unit -> t

    (** [make_former former] returns the abbreviation type representing the
        type former [former]. *)
    val make_former : t former -> t
  end

  module Abbreviations : sig
    (** [t] represents the abbreviation context. *)
    type t

    (** [empty] is the abbreviation context containing no abbreviations *)
    val empty : t

    (** [add t ~abbrev] adds the abbreviation [abbrev] to [t] --
        an abbreviation is a pair [('a1, ..., 'an) former = type_]. *)
    val add : t -> abbrev:Abbrev_type.t former * Abbrev_type.t -> t
  end

  module Equations : sig
    (** [t] represents the equational context. *)
    type t

    (** [empty] is the empty equational context -- containing
        no equations. *)
    val empty : t

    exception Inconsistent

    (** [add ~state ~abbrev_ctx t type1 type2] adds the equality [type1 = type2] to
        the equational context [t] -- [abbrev_ctx] is used to determine the required equalities
        (modulo the abbreviation context) and [state] is used for equational scoping purposes. *)
    val add
      :  state:state
      -> abbrev_ctx:Abbreviations.t
      -> t
      -> Rigid_type.t
      -> Rigid_type.t
      -> t
  end

  module Structure : sig
    include Structure.S

    (** ['a repr] external representation of a ['a t] *)
    type 'a repr =
      | Flexible_var
      | Row_uniform of 'a
      | Row_cons of label * 'a * 'a
      | Rigid_var of Rigid_var.t
      | Former of 'a former

    (** [repr structure] returns to representation of [structure] *)
    val repr : 'a t -> 'a repr
  end

  module Unifier : sig
    include Unifier.S with type 'a structure = 'a Structure.t

    type ctx =
      { abbrev_ctx : Abbreviations.t
      ; equations_ctx : Equations.t
      }

    val empty_ctx : ctx
    val unify : state:state -> ctx:ctx -> Type.t -> Type.t -> unit
  end

  open Unifier

  (** [make_rigid_var ~state rigid_var] creates rigid unification variable. *)
  val make_rigid_var : state:state -> Rigid_var.t -> Type.t

  (** [make_flexible_var ~state] creates a flexible unification variable. *)
  val make_flexible_var : state:state -> Type.t

  (** [make_former ~state former] creates a unification type w/ former [former]. *)
  val make_former : state:state -> Type.t former -> Type.t

  (** [make_row_uniform ~state type_] creates a unification row w/ row [∂(type_)] *)
  val make_row_uniform : state:state -> Type.t -> Type.t

  (** [make_row_cons ~state ~label ~field ~tl] creates a unification row w/ row [(label : field; tl)] *)
  val make_row_cons
    :  state:state
    -> label:label
    -> field:Type.t
    -> tl:Type.t
    -> Type.t

  (** The type [scheme] defines the abstract notion of a scheme in
      "graphic" types.

      A scheme has a notion of "bound" variables, this is encoded in the
      type [variables].

      We note that all bound variables to a *generalized* scheme
      are *rigid*. *)

  type scheme

  (** The notion of "bound" variables for a scheme is shared between
      instantiation and computing the set of generic variables,
      given a scheme. *)

  type variables = Type.t list

  (** [root scheme] returns the root node, or quantifier "body" of the
      scheme [scheme]. *)
  val root : scheme -> Type.t

  (** [variables scheme] computes the bound variables of a scheme [scheme]. *)
  val variables : scheme -> variables

  (** [mono_scheme] creates a scheme with no generic variables. *)
  val mono_scheme : Type.t -> scheme

  (** [enter ~state] creates a new "stack frame" in the constraint solver
      and enters it. *)

  val enter : state:state -> unit

  (** [instantiate ~state scheme] instantates the scheme [scheme]. It does so, by
      taking fresh copies of the generic variables, without necessarily
      copying other bits of the type.

      This is designed for efficient sharing of nodes within the
      "graphic type". *)
  val instantiate : state:state -> scheme -> variables * Type.t

  exception Cannot_flexize of Rigid_var.t
  exception Rigid_variable_escape of Rigid_var.t
  exception Scope_escape of Type.t

  val exit
    :  state:state
    -> rigid_vars:Rigid_var.t list
    -> types:Type.t list
    -> variables * scheme list
end

(** The interface of {generalization.ml}. *)

module type Intf = sig
  module type S = S

  (** The functor [Make]. *)
  module Make (Label : Comparable.S) (Former : Type_former.S) :
    S with type 'a former := 'a Former.t and type label := Label.t
end
