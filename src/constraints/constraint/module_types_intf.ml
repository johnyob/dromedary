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

(** This module implements the interfaces for the constraints *)

open Base

module type Term_var = sig
  (** The type [t] of term variables [x, y, ...] in the term algebra. *)
  type t [@@deriving sexp_of, compare]
end

module type Type_var = sig
  (** The type [t] of reconstucted type variables. In [??], F. Pottier defines 
      [t] as [int]. *)
  type t [@@deriving sexp_of]

  (** [of_int n] returns the unique type variable mapped to by [n]. *)
  val of_int : int -> t
end

module Type_former = struct
  module type Basic = sig
    (** The type ['a t] defines the type former w/ children of type ['a]. 
    
        It is a functor, the fixpoint of ['a t] defines the set of 
        types. See {!Type} 
    *)
    type 'a t [@@deriving sexp_of]

    val id : 'a t -> int

    (** ['a t] is a traversable, hence is foldable and a functor. See Haskell type classes. *)
    module Traverse (F : Applicative.S) : sig
      val traverse : 'a t -> f:('a -> 'b F.t) -> 'b t F.t

      val traverse2
        :  'a t
        -> 'b t
        -> f:('a -> 'b -> 'c F.t)
        -> [ `Ok of 'c t F.t | `Unequal_structure ]
    end
  end

  module type S = sig
    type 'a t [@@deriving sexp_of]

    val id : 'a t -> int

    val map : 'a t -> f:('a -> 'b) -> 'b t
    val fold : 'a t -> f:('a -> 'b -> 'b) -> init:'b -> 'b
    val iter : 'a t -> f:('a -> unit) -> unit

    exception Iter2

    val iter2_exn : 'a t -> 'b t -> f:('a -> 'b -> unit) -> unit

    exception Fold2

    val fold2_exn : 'a t -> 'b t -> f:('a -> 'b -> 'c -> 'c) -> init:'c -> 'c
  end
end

module type Type = sig
  (* Abstract types to be substituted by functor arguments. *)

  type variable
  type 'a former

  (** A concrete representation of types. This is the *free monad* of
      [Former.t] with variables [Var.t], defined by the grammar:
        t ::= 'a | t F
  
      We could define [t] using an *explicit fixpoint*: 
      type t = 
        | Var of Var.t
        | Former of t Former.t

      However, we leave [t] abstract, since OCaml doesn't have pattern 
      synonyms, making explicit fixpoints unwieldy.

      For constructors of [t]. See {!var}, {!former}. 
  *)

  type t [@@deriving sexp_of]

  (** [var 'a] is the representation of the type variable ['a] as the 
      type [t]. *)

  val var : variable -> t

  (** [former f] is the representation of the concrete type former [f] in
      type [t]. *)
  val former : t former -> t

  (** [mu a t] is the representation of the recursive type [μ a. t].
      While Dromedary doesn't support recursive types, we use them for
      printing cyclic types (e.g. when using [Cycle]).  
  *)
  val mu : variable -> t -> t
end

module type Types = sig
  (** Type variables used for type reconstruction. *)
  module Var : Type_var

  (** Type formers used for type reconstruction. Used by the Unifier. *)
  module Former : Type_former.S

  (** Types used for type reconstruction. *)
  module Type :
    Type with type variable := Var.t and type 'a former := 'a Former.t

  (** A scheme [scheme] is defined as by the grammar: σ ::= τ | ∀ ɑ. σ *)
  type scheme = Var.t list * Type.t
end

module type Algebra = sig
  module Term_var : Term_var
  module Types : Types
end

module type Intf = sig
  module type Type_var = Type_var
  module type Term_var = Term_var

  module Type_former : sig
    include module type of Type_former
    module Make (T : Basic) : S with type 'a t := 'a T.t
  end

  module type Type = Type
  module type Types = Types
  module type Algebra = Algebra
end
