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

(** This module implements the interfaces for the constraints, defined 
    by F. Pottier in [??]. *)

(** This is the signature of term variables used in constraints and 
    the constraint solver. *)

module type Term_var = sig
  (** The type [t] of term variables [x, y, ...] in the term algebra. *)
  type t [@@deriving sexp_of, compare]
end

(** This is the signature of types used in the unifier. *)

module type Type_var = sig
  (** The type [t] of reconstucted type variables. 
  
      In [??], F. Pottier defines [t] as [int]. *)
  type t [@@deriving sexp_of]

  (** [of_int n] returns the unique type variable mapped to by [n]. *)
  val of_int : int -> t
end

module type Type_former = sig
  (** The type ['a t] defines the type former w/ children of type ['a]. 
  
      It is a functor, the fixpoint of ['a t] defines the set of 
      types. See {!Type} *)
  type 'a t [@@deriving sexp_of]

  (* The type ['a t] has an associated [map] operation (satisfying the 
     functor laws). *)
  val map : 'a t -> f:('a -> 'b) -> 'b t

  (* [fold], [iter], and [iter2] are also required by F. Pottier [??]. *)
  val iter : 'a t -> f:('a -> unit) -> unit
  val fold : 'a t -> f:('a -> 'b -> 'b) -> init:'b -> 'b

  (* Exceptions are faster than returning variants *)
  exception Iter2

  val iter2 : 'a t -> 'b t -> f:('a -> 'b -> unit) -> unit
end

module type Type = sig
  (* Abstract types to be substituted by functor arguments. *)

  type var
  type 'a former

  (** A concrete representation of types. This is the *free monad* of
      [Former.t] with variables [Var.t], defined by the grammar:
        t ::= 'a | t F
  
      We could define [t] using an *explicit fixpoint*: 
      type t = 
        | Var of Var.t
        | Form of t Former.t

      However, we leave [t] abstract, since OCaml doesn't have pattern 
      synonyms, making explicit fixpoints unwieldy.
      
      For constructors of [t]. See {!var}, {!form}. *)

  type t [@@deriving sexp_of]

  (** [var 'a] is the representation of the type variable ['a] as the 
      type [t]. See [Var] above. *)

  val var : var -> t

  (** [form f] is the representation of the concrete type former [f] in
      type [t]. See [Form] above. *)
  val form : t former -> t
end

(** This is the signature of types after reconstruction *)

module type Types = sig
  (** Type variables used for type reconstruction. *)
  module Var : Type_var

  (** Type formers used for type reconstruction. Used by the Unifier. *)
  module Former : Type_former

  (** Types used for type reconstruction. *)
  module Type : Type with type var := Var.t and type 'a former := 'a Former.t

  (** A scheme [scheme] is defined as by the grammar:
        \sigma ::= \tau | \forall a. \tau
      In OCaml, we encode this using a list of variables and a type. *)
  type scheme = Var.t list * Type.t
end

(** This is the signature for the entire language (algebra) *)

module type Algebra = sig

  module Term_var : Term_var

  module Types : Types
end


