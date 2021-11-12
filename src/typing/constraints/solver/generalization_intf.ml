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

open Constraint.Intf

(* ----------------------------------------------------------------------- *)

module type S = sig
  (** Abstract types to be substituted by functor arguments. *)

  (** The type ['a former] is the type formers (with children of type ['a]), 
      given by the functor argument [Former]. *)

  type 'a former

  (* ----------------------------------------------------------------------- *)

  (* Instantiating the unifier *)

  module Tag : sig
    type t [@@deriving sexp_of]
  end

  module Unifier :
    Unifier.S with type 'a former := 'a former and type metadata := Tag.t

  (* ----------------------------------------------------------------------- *)

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

  type variables = Unifier.Type.t list

  (** [root sch] returns the root node, or quantifier "body" of the
      scheme [sch]. *)
  val root : scheme -> Unifier.Type.t

  (** [variables sch] computes the bound variables of a scheme [sch]. *)
  val variables : scheme -> variables

  (** [monoscheme] creates a scheme with no generic variables. *)
  val monoscheme : Unifier.Type.t -> scheme

  (* ----------------------------------------------------------------------- *)

  (** The generalization module maintains several bits of mutable
      state related to it's implemented of efficient level-based
      generalization.
    
      We encapsulate this in the abstract type [state]. 
     
      The current level (the number of stack frames used in the abstract
      constraint solver) and the regions (1 region for each stack frame,
      containing the bound variables). 
      
      TODO: Relate this to the abstract machine we define in the 
      dissertation. *)

  type state

  (** [make_state ()] creates a new empty state. *)
  val make_state : unit -> state

  (** [enter state] creates a new "stack frame" in the constraint solver
     and enters it.  *)

  val enter : state -> unit


  (** [fresh_var] creates a fresh unification variable. *)

  val fresh_var : state -> Unifier.Type.flexibility -> Unifier.Type.t

  (** [fresh_form] creates a fresh unification type node 
      w/ the structure provided by the former. *)

  val fresh_form : state -> Unifier.Type.t former -> Unifier.Type.t

  (* ----------------------------------------------------------------------- *)

  (** [instantiate sch] instantates the scheme [sch]. It does so, by
      taking fresh copies of the generic variables, without necessarily
      copying other bits of the type. 
      
      This is designed for efficient sharing of nodes within the
      "graphic type". *)

  val instantiate : state -> scheme -> variables * Unifier.Type.t

  exception Rigid_var_escape

  val exit
    :  state
    -> rigid_vars: Unifier.Type.t list
    -> roots: Unifier.Type.t list
    -> variables * scheme list
end

(* ------------------------------------------------------------------------- *)

(* The interface of {generalization.ml}. *)

module type Intf = sig
  module type S = S

  (* The functor [Make]. *)
  module Make (Former : Type_former) : S with type 'a former := 'a Former.t
end
