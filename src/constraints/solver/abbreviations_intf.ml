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

module type S = sig
  (** Abstract types to be substituted by functor arguments. *)

  (** The type ['a former] is the type formers (with children of type ['a]), 
      given by the functor argument [Former]. *)
  type 'a former

  module Type : sig
    (** [t] represents a graphical encoding of an abbreviational type *)
    type t [@@deriving sexp_of, compare]

    type structure =
      | Var
      | Former of t former

    (** [id t] is a unique identifier for the type [t]. (used for hashing, etc) *)
    val id : t -> int

    (** [get_structure t] returns the structure of [t]. *)
    val get_structure : t -> structure

    (** [hash] is an alias for [id] (required for [Hash_key] intf). *)
    val hash : t -> int

    val make_var : unit -> t
    val make_former : t former -> t
  end

  module Abbreviation : sig
    type t

    type productivity =
      | Non_productive of int
      | Productive of Type.t former

    val make
      :  former:_ former
      -> rank:int
      -> decomposable_positions:int list
      -> productivity:productivity
      -> type_:Type.t list * Type.t former
      -> t
  end

  module Ctx : sig
    (** type [t] encodes the abbreviation context, mapping [_ former]s to 
        abbreviations. *)
    type t

    (** [empty] is the empty type abbreviation context.  *)
    val empty : t

    val add : t -> abbrev:Abbreviation.t -> t
    val has_abbrev : t -> _ former -> bool

    exception Not_found

    type productivity =
      | Non_productive of int
          (** [Non_productive i] encodes that the abbreviation expands to [aᵢ] *)
      | Productive
          (** [Productive] encodes that the former has a productive abbreviation *)

    (** [get_productivity t former] returns whether the productivity of the 
        former [former] in the context [t]. Raises [Not_found] if former is primitive. *)
    val get_productivity : t -> _ former -> productivity

    (** [get_expansion t former] returns the expansion of [former] in context. 
        Raises [Not_found] is [former] has no expansion *)
    val get_expansion : t -> _ former -> Type.t list * Type.t former

    (** [decomposable_positions t former] returns the decomposable positions
        of [former]. *)
    val get_decomposable_positions : t -> _ former -> int list

    (** [get_rank t former] returns the rank of the former in [t]. *)
    val get_rank : t -> _ former -> int

    (** [clash t former1 former2] returns [true] if [former1] and [former2] are not
      equivalent under context [t]. *)
    val clash : t -> _ former -> _ former -> bool
  end
end

module type Intf = sig
  module type S = S

  module Make (Former : Type_former.S) : S with type 'a former := 'a Former.t
end