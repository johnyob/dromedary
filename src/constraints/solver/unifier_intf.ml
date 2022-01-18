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

(** For abstraction purposes, we wrap all data not related to unification in an 
    abstract "metadata" type. 
    
    A concrete example of this metadata would be the level used in 
    generalization. See {!generalization.mli}. 
      
    This abstraction forms a commutative monoid. 
*)

module Metadata = struct
  module type S = sig
    (** [t] is the abstract type of the metadata associated with each types. *)

    type t [@@deriving sexp_of]

    (** [merge] is performed when unifying two types. 
      We assume that [merge] is associative and commutative. *)
    val merge : t -> t -> t
  end

  module type S1 = sig
    (** [t] is the abstract type of the metadata associated with each types. *)

    type 'a t [@@deriving sexp_of]

    (** [merge] is performed when unifying two types. 
        We assume that [merge] is associative and commutative. *)
    val merge : 'a t -> 'a t -> 'a t
  end
end

module type Ctx = sig
  type 'a t [@@deriving sexp_of]
end

module type Former = sig
  type 'a t [@@deriving sexp_of]

  module Ctx : Ctx

  val map : 'a t -> f:('a -> 'b) -> 'b t
  val fold : 'a t -> f:('a -> 'b -> 'b) -> init:'b -> 'b
  val iter : 'a t -> f:('a -> unit) -> unit

  exception Iter2

  val iter2_exn : ctx:'a Ctx.t -> 'a t -> 'a t -> f:('a -> 'a -> unit) -> unit
end

module type S = sig
  (** Abstract types to be substituted by functor arguments. *)

  (** The type ['a former] is the type formers (with children of type ['a]), 
      given by the functor argument [Former]. *)
  type 'a former

  (** The type ['a ctx] is the arbitrary context used by formers. *)
  type 'a ctx

  (** [metadata] is the type of metadata, given by the functor argument
      [Metadata]. *)
  type 'a metadata

  module Rigid_var : sig
    type t [@@deriving sexp_of, compare]

    val id : t -> int
    val hash : t -> int
    val make : unit -> t
  end


  module Type : sig
    (** [t] represents a type. See "graphical types". *)
    type t [@@deriving sexp_of, compare]

    type structure =
      | Flexible_var
      | Rigid_var of Rigid_var.t
      | Former of t former

    type nonrec metadata = t metadata

    val to_dot : t -> string

    (** [id t] returns the unique identifier of the type [t]. *)
    val id : t -> int

    (** [get_structure t] returns the structure of [t]. *)
    val get_structure : t -> structure

    (** [set_structure t structure] sets the structure of [t] to [structure]. *)
    val set_structure : t -> structure -> unit

    (** [get_metadata t] returns the metadata of [t]. *)
    val get_metadata : t -> metadata

    (** [set_metadata t metadata] sets the metadata of [t] to [metadata]. *)
    val set_metadata : t -> metadata -> unit

    (** [hash t] computes the hash of the graphical type [t]. 
     Based on it's integer field: id. *)
    val hash : t -> int

    (** [make_var metadata] returns a fresh flexible variable with metadata [metadata]. *)
    val make_flexible_var : metadata -> t

    val make_rigid_var : Rigid_var.t -> metadata -> t

    (** [make_former former metadata] returns a fresh type former
        with metadata [metadata]. *)
    val make_former : t former -> metadata -> t

    exception Cannot_flexize of t

    (** [flexize ~src ~dst] performs flexization on [src], "linking" it to [dst].
        Raises [Cannot_flexize] if [src] is not a rigid variable. *)
    val flexize : src:t -> dst:t -> unit
  end

  (** [unify ~ctx t1 t2] equates the graphical type nodes [t1] and [t2], 
      and forms a multi-equation node.
      
      Identifiers are merged arbitrarily.

      Formers are unified recursively, using [iter2]. 
      
      Metadata are merged using [Metadata.merge].

      [Unify (t1, t2)] is raised if the two node cannot
      be unified. This occurs with rigid variables or incompatable
      formers. 

      No occurs check is implemented (this is separate from 
      unification). See {!occurs_check}. 
  *)

  exception Unify of Type.t * Type.t

  val unify : ctx:Type.t ctx -> Type.t -> Type.t -> unit

  (** [occurs_check t] detects whether there is a cycle in 
      the graphical type [t]. 
      
      If a cycle is detected, [Cycle t] is raised. 
  *)

  exception Cycle of Type.t

  val occurs_check : Type.t -> unit

  (* (** [fold_acyclic type_ ~var ~former] will perform a bottom-up fold
      over the (assumed) acyclic graph defined by the type [type_]. *)
  val fold_acyclic
    :  Type.t
    -> var:(Type.t -> 'a)
    -> former:('a former -> 'a)
    -> 'a

  (** [fold_cyclic type_ ~var ~former ~mu] will perform a fold over
      the (potentially) cyclic graph defined by the type [type_]. *)
  val fold_cyclic
    :  Type.t
    -> var:(Type.t -> 'a)
    -> former:('a former -> 'a)
    -> mu:(Type.t -> 'a -> 'a)
    -> 'a *)
end

(** The interface of {unifier.ml}. *)

module type Intf = sig
  module Metadata = Metadata
  module type Former = Former
  module type S = S

  (** The functor [Make]. *)
  module Make (Former : Former) (Metadata : Metadata.S1) :
    S
      with type 'a former := 'a Former.t
       and type 'a ctx := 'a Former.Ctx.t
       and type 'a metadata := 'a Metadata.t
end