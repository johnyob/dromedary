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

(* This module implements signatures used by the unifier. *)

open Base

module type S = sig
  (** Abstract types to be substituted by functor arguments. *)

  (** The type ['a structure] is the unification structures (with children of type ['a]), 
      given by the functor argument [Structure]. *)
  type 'a structure

  (** The type [ctx] is the arbitrary unification context determined by
      the structure's context, given by [Structure]. *)
  type 'a ctx

  module Type : sig
    (** [t] represents a type. See "graphical types". *)
    type t [@@deriving sexp_of, compare]

    (* Uses human representation (warning, may print cycles!) *)
    val sexp_of_t_hum : t -> Sexp.t

    (** Each graphical type node consists of:
        - a unique identifier [id] (used to define a total ordering).
        - a mutable [structure], which contains the node structure. *)

    (** [id t] returns the unique identifier of the type [t]. *)
    val id : t -> int

    (** [structure t] returns the structure of [t]. *)
    val structure : t -> t structure

    (** [set_structure t structure] sets the structure of [t] to [structure]. *)
    val set_structure : t -> t structure -> unit

    (** [hash t] computes the hash of the graphical type [t]. 
        Based on it's integer field: id. *)
    val hash : t -> int

    (** [make structure] creates a new unification type w/ structure [structure]. *)
    val create : t structure -> t

    (** [fold t ~f ~var ~mu] will perform a fold over
      the (potentially) cyclic graph defined by the type [t]. *)
    val fold
      :  t
      -> f:(t -> 'a structure -> 'a)
      -> var:(t -> 'a)
      -> mu:(t -> 'a -> 'a)
      -> 'a

    (** [to_dot t] returns the graph-viz .dot encoding of [t]. *)
    val to_dot : t -> string

    (** [reset_id_cnt ()] resets the internal counter used for [id]. *)
    val reset_id_cnt : unit -> unit
  end

  (** [unify ~ctx t1 t2] equates the graphical type nodes [t1] and [t2], 
      and forms a multi-equation node.
      
      [Unify (t1, t2)] is raised if the two node cannot
      be unified. *)

  exception Unify of Type.t * Type.t

  val unify : ctx:Type.t ctx -> Type.t -> Type.t -> unit
end

(** The interface of {unifier.ml}. *)

module type Intf = sig
  module type S = S

  (** The functor [Make]. *)
  module Make (Structure : Structure.S) :
    S with type 'a structure = 'a Structure.t and type 'a ctx = 'a Structure.ctx
end