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

(* ------------------------------------------------------------------------- *)

(** This is the signature of term variables used in constraints and 
    the constraint solver. *)

module type Term_var = sig
  (* The type of term variables. *)
  type t [@@deriving sexp_of, compare]

  (* Term variables are sexp-able for pretty printing and error reporting.  *)

  (* Term variables have a total ordering. *)
end

(* ------------------------------------------------------------------------- *)

(** This is the signature of types used in the unifier. *)

module type Type_var = sig
  (* The reconstucted type variable. F. Pottier defines this as [int] in [??]. 
     We leave it abstract, providing a morphism from [int] to [t]. *)
  type t [@@deriving sexp_of]

  (* Type variables are sexp-able for pretty printing and error reporting.  *)

  val of_int : int -> t
end

module type Type_former = sig
  (* The type ['a t] is a functor, where ['a] denotes a recursive parameter.
     The fixpoint of ['a t] defines the set of types. See {!Type} *)
  type 'a t [@@deriving sexp_of]

  (* Formers are sexp-able for pretty printing and error reporting.  *)

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

  (* A concrete representation of types. This is the *free monad* of
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

  (* [var 'a] is the representation of the type variable ['a] as the 
    type [t]. See [Var] above. *)

  val var : var -> t

  (* [form f] is the representation of the concrete type former [f] in
    type [t]. See [Form] above. *)
  val form : t former -> t
end

(** This is the signature of types after reconstruction *)

module type Types = sig
  (* Type variables used for type reconstruction. *)
  module Var : Type_var

  (* Type formers used for type reconstruction. Used by the Unifier. *)
  module Former : Type_former

  (* Types used for type reconstruction. *)
  module Type : Type with type var := Var.t and type 'a former := 'a Former.t

  type scheme = Var.t list * Type.t
end

