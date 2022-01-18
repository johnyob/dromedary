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

(* This module implements signatures used by the unifier to implement 
   type abbreviations. *)

open! Import

module type View = sig
  (** ['a t] encodes a view of ['a former]s. *)
  type 'a t [@@deriving sexp_of]

  (** ['a repr] encodes the representative of the view *)
  type 'a repr

  val repr : 'a t -> 'a repr
  val iter : 'a t -> f:('a -> unit) -> unit
  val fold : 'a t -> f:('a -> 'b -> 'b) -> init:'b -> 'b
end

module type S = sig
  (** Abstract types to be substituted by functor arguments. *)

  (** The type ['a former] is the type formers (with children of type ['a]), 
      given by the functor argument [Former]. *)
  type 'a former

  type metadata

  module Abbrev_type : sig
    (** [t] represents a graphical encoding of an abbreviational type *)
    type t [@@deriving sexp_of, compare]

    type structure =
      | Var
      | Former of t former

    (** [make_var ()] returns a fresh abbreviation type variable. *)
    val make_var : unit -> t

    (** [make_former former] returns a fresh abbreviation former for [former]. *)
    val make_former : t former -> t
  end

  module Abbreviation : sig
    type t

    val make
      :  former:_ former
      -> rank:int
      -> decomposable_positions:int list
      -> productivity:
           [ `Non_productive of int | `Productive of Abbrev_type.t former ]
      -> type_:Abbrev_type.t list * Abbrev_type.t former
      -> t
  end

  module Non_productive_view : View with type 'a repr := 'a former option
  module Productive_view : View with type 'a repr := 'a former

  (** ['a ctx] is the context used for type abbreviations within the unifier *)
  type 'a ctx

  module Metadata : sig
    type 'a t =
      { non_productive_view : 'a Non_productive_view.t
      ; metadata : metadata
      }
    [@@deriving sexp_of]
  end

  module Unifier :
    Unifier.S
      with type 'a former := 'a Productive_view.t
       and type 'a ctx := 'a ctx
       and type 'a metadata := 'a Metadata.t

  module Ctx : sig
    type t
    val empty : t
    val add : t -> abbrev:Abbreviation.t -> t
  end

  val unify : ctx:Ctx.t -> metadata:(unit -> metadata) -> Unifier.Type.t -> Unifier.Type.t -> unit

  val make_flexible_var : metadata -> Unifier.Type.t
  val make_rigid_var : Unifier.Rigid_var.t -> metadata -> Unifier.Type.t

  val make_former
    :  ctx:Ctx.t
    -> Unifier.Type.t former
    -> metadata
    -> Unifier.Type.t
end

module type Intf = sig
  module type S = S

  module Make (Former : Type_former.S) (Metadata : Unifier.Metadata.S) :
    S with type 'a former := 'a Former.t and type metadata := Metadata.t
end
