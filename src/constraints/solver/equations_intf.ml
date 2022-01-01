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

  module Unifier :
    Unifier.S with type 'a former := 'a former and type metadata := metadata

  (** An equation [t : Equation.t] denotes some arbitrary equality. 
      
      We leave it's implementation and type abstract to provide a foundation
      for more efficient implementations. 
  *)
  module Equation : sig
    type t [@@deriving sexp_of]

    (** [type1 =. type2] returns an equation that encodes the equality 
        between [type1] and [type2]. *)
    val ( =. ) : Unifier.Type.t -> Unifier.Type.t -> t
  end

  (** [t] defines an arbitrary context of equations. *)
  type t

  exception Inconsistent

  (** [add_equation t equation] adds the equation [equation] to [t]. 
      [Inconsistent] is raised if we can deduce false from the context [t; equation]. 
  *)
  val add_equation : t -> Equation.t -> t

  (** [equivalent t type1 type2] determines whether types [type1] and [type2] are equivalent
      under the context [t].  
  *)
  val equivalent : t -> Unifier.Type.t -> Unifier.Type.t -> bool

end

(** The interface of {equations.ml}. *)

module type Intf = sig
  module type S = S

  (** The functor [Make]. *)
  module Make (Former : Type_former.S) (Metadata : Unifier.Metadata) :
    S with type 'a former := 'a Former.t and type metadata := Metadata.t
end