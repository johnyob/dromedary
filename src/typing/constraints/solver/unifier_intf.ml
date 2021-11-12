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

(* Unification consists of solving equations between types. 
   For generalization and efficiency, we use "multi-equations":
     e ::= [] | t = e
   
   A multi-equation is standard iff it contains 1 non-variable member,
   known as the [terminal]. *)

open Constraint.Intf

open Base

(* ------------------------------------------------------------------------- *)

(* For abstract purposes, we wrap all data not related to unification in an 
   abstract "metadata" type. 
    
   A concrete example of this metadata would be the level used in 
   generalization. See {!generalization.mli}. 
    
   This abstraction forms a commutative monoid. *)

module type Metadata = sig
  (* [t] is the abstract type of the metadata associated with each variable. *)

  type t [@@deriving sexp_of]

  (* [merge] is performed when unifying two variables. 
     We assume that [merge] is associative and commutative. *)

  val merge : t -> t -> t
end

(* ------------------------------------------------------------------------- *)

(* This functor describes the signatures of the unifier.  *)

module type S = sig
  (* Abstract types to be substituted by functor arguments. *)

  type 'a former
  type metadata

  module Type : sig

    (* There are two kinds of variables. A [Flexible] variable can
       be unified with other variables and types. A [Rigid] (in general) 
       cannot be unified. *)

    type flexibility =
      | Flexible
      | Rigid
    [@@deriving sexp_of, eq]

    (* sexp-able for error reporting and prettying printing. *)

    type t [@@deriving sexp_of, compare]

    type structure = 
      | Var of { mutable flexibility : flexibility }
      | Form of t former

    (* Each graph type node consists of:
        - a unique identifier [id] (used to define a total ordering).
        - a mutable [structure], which contains the node structure.
        - a mutable piece of [metadata]. 
        
      They are accessed via setters and getters: *)

    val id : t -> int
    
    val get_structure : t -> structure
    val set_structure : t -> structure -> unit
    
    val get_metadata : t -> metadata
    val set_metadata : t -> metadata -> unit    

    (* [hash t] computes the hash of the graph type node [t]. 
       Based on it's integer field: id. *)

    val hash : t -> int

  end

  val fresh 
    :  Type.structure
    -> metadata
    -> Type.t

  (* [fresh_var flex data] returns a fresh variable node 
     with flexibility [flex], and metadata [data]. *)

  val fresh_var
    :  Type.flexibility
    -> metadata
    -> Type.t

  (* [fresh_form form data] returns a fresh type former node
    with metadata [data]. *)

  val fresh_form
    :  Type.t former
    -> metadata
    -> Type.t

  (* [unify t1 t2] equates the graph type nodes [t1] and [t2], 
     and forms a multi-equation node.
      
     Identifiers are merged arbitrarily. 
     Formers are unified recursively, using [iter2]. 
     Metadata are merged using [Metadata.merge].

     [Unify (t1, t2)] is raised if the two node cannot
     be unified. This occurs with rigid variables or incompatable
     formers. 

     No occurs check is implemented (this is separate from 
     unification). See {!occurs_check}. *)

  exception Unify of Type.t * Type.t

  val unify : Type.t -> Type.t -> unit

  (* [occurs_check t] detects whether there is 
      a cycle in the graph type [t]. 
      
      If a cycle is detected, [Cycle t] is raised. *)

  exception Cycle of Type.t

  val occurs_check : Type.t -> unit

  (* [fold typ ~var ~form] will perform a bottom-up fold
    over the (assumed) acyclic graph defined by the type [typ].  *)

  val fold
  :  Type.t
  -> var:(Type.t -> Type.flexibility -> 'a)
  -> form:('a former -> 'a)
  -> 'a

end

(* ------------------------------------------------------------------------- *)

(* The interface of {unifier.ml}. *)

module type Intf = sig
  module type Metadata = Metadata
  module type S = S

  (* The functor [Make]. *)
  module Make (Former : Type_former) (Metadata : Metadata) :
    S with type 'a former := 'a Former.t and type metadata := Metadata.t
end