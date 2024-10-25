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
        types. See {!Type} *)
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

module type Types = sig
  (** Type variables, used for type recon *)
  module Var : Type_var

  (** Type formers used for type reconstruction. Used by the Unifier. *)
  module Former : Type_former.S

  (** Labels for row types. *)
  module Label : Comparable.S
end

module type Decoded_var = sig
  type t [@@deriving sexp_of]

  val make : unit -> t
  val id : t -> int
end

module type Decoded_type = sig
  type variable
  type label
  type 'a former

  (** [t] describes the decoded type *)
  type t [@@deriving sexp_of]

  (** [desc] is an "external" descriptor -- which may be used
      to decode the type. *)
  type 'a desc =
    | Var of variable
    | Former of 'a former
    | Row_cons of label * 'a * 'a
    | Row_uniform of 'a
  [@@deriving sexp_of]

  (** Decoded types may be cyclic -- so we require an [id] *)
  val id : t -> int

  (** [desc t] returns the descriptor of [t] *)
  val desc : t -> t desc

  (** [make desc] creates the decoded type with descriptor [desc] *)
  val make : t desc -> t

  (** [mu a t] returns the equi-recursive (cyclic) type
      w/ body [t] binding [a] cyclically. *)
  val mu : variable -> t -> t

  val let_ : binding:variable * t -> in_:t -> t

  val fold
    :  t
    -> f:('a desc -> 'a)
    -> mu:(variable -> 'a -> 'a)
    -> var:(variable -> 'a)
    -> 'a
end

module type Decoded = sig
  type label
  type 'a former

  module Var : Decoded_var

  module Type :
    Decoded_type
    with type label := label
     and type variable := Var.t
     and type 'a former := 'a former

  type scheme = Var.t list * Type.t [@@deriving sexp_of]
end

module type Algebra = sig
  module Term_var : Term_var
  module Types : Types
end

module type Algebra_with_decoded = sig
  include Algebra

  module Decoded :
    Decoded
    with type label := Types.Label.t
     and type 'a former := 'a Types.Former.t
end

module type Intf = sig
  module type Type_var = Type_var
  module type Term_var = Term_var

  module Type_former : sig
    include module type of Type_former
    module Make (T : Basic) : S with type 'a t := 'a T.t
  end

  module type Types = Types
  module type Decoded = Decoded
  module type Algebra = Algebra
  module type Algebra_with_decoded = Algebra_with_decoded
end
