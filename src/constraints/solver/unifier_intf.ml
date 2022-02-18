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

(** Unification consists of solving equations between types. 
    For generalization and efficiency, we use "multi-equations":
      e ::= [] | t = e
   
    A multi-equation is standard iff it contains 1 non-variable member,
    known as the [terminal]. 
*)

open! Import

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

    val to_dot : t -> string

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
    val make : t structure -> t
  end

  (** [unify ~ctx t1 t2] equates the graphical type nodes [t1] and [t2], 
      and forms a multi-equation node.
      
      [Unify (t1, t2)] is raised if the two node cannot
      be unified. 

      No occurs check is implemented (this is separate from 
      unification). See {!occurs_check}. *)

  exception Unify of Type.t * Type.t

  val unify : ctx:Type.t ctx -> Type.t -> Type.t -> unit

  (** [occurs_check t] detects whether there is a cycle in 
      the graphical type [t]. 
      
      If a cycle is detected, [Cycle t] is raised. *)

  exception Cycle of Type.t

  val occurs_check : Type.t -> unit

  (** [fold_acyclic type_ ~f] will perform a bottom-up fold
      over the (assumed) acyclic graph defined by the type [type_]. *)
  val fold_acyclic : Type.t -> f:(Type.t -> 'a structure -> 'a) -> 'a

  (** [fold_cyclic type_ ~f ~var ~mu] will perform a fold over
      the (potentially) cyclic graph defined by the type [type_]. *)
  val fold_cyclic
    :  Type.t
    -> f:(Type.t -> 'a structure -> 'a)
    -> var:(Type.t -> 'a)
    -> mu:(Type.t -> 'a -> 'a)
    -> 'a
end

(** The interface of {unifier.ml}. *)

module type Intf = sig
  module type S = S

  (** The functor [Make]. *)
  module Make (Structure : Structure_intf.S) :
    S with type 'a structure = 'a Structure.t and type 'a ctx = 'a Structure.ctx
end