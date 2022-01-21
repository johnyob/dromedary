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

(* This module implements signatured used for unification structures. *)

open! Import

module type S = sig
  (** A structure defines the "structure" of the unification type.
      Namely, the unification type is given by the fixed point of the 
      functor ['a structure].
      
      Some examples of structures include:
      - First order terms
      - Rigid first terms
      - Rows
      - Ambivalence
  *)
  type 'a t [@@deriving sexp_of]

  val map : 'a t -> f:('a -> 'b) -> 'b t
  val iter : 'a t -> f:('a -> unit) -> unit
  val fold : 'a t -> f:('a -> 'b -> 'b) -> init:'b -> 'b

  (** Structures must exhibit [merge], which is the ability
      to compute a logically consistent structure from 2 structures. 

      If the 2 structures are not consistent, then we raise [Cannot_merge].
      
      Consistency is determined via the ability to emit first-order equalities,
      provided by [equate].

      In some cases, logical consistency of 2 structures requires a context. 
      (e.g. Abbreviations, and Ambivalence), thus [merge] requires a
      context [ctx]. 
      
      In some cases, consistency may also a notion of "expansiveness", the ability
      to create new terms during [merge]. This is defined in the context ['a expansive]
  *)

  type 'a expansive
  type ctx

  exception Cannot_merge

  val merge
    :  expansive:'a expansive
    -> ctx:ctx
    -> equate:('a -> 'a -> unit)
    -> 'a t
    -> 'a t
    -> 'a t
end

module type Intf = sig
  module type S = S

  module Rigid_var : sig
    type t = private int [@@deriving sexp_of, compare]

    val make : unit -> t
    val hash : t -> int
  end

  module Of_former (Former : Type_former.S) : sig
    type 'a t = 'a Former.t

    include S with type 'a t := 'a t and type ctx = unit and type 'a expansive = unit
  end

  module First_order (S : S) : sig
    type 'a t =
      | Var
      | Structure of 'a S.t

    include
      S
        with type 'a t := 'a t
         and type ctx = S.ctx
         and type 'a expansive = 'a S.expansive
  end

  module Ambivalent (S : S) : sig
    module Rigid_type : sig
      type t =
        | Rigid_var of Rigid_var.t
        | Structure of t S.t
    end

    module Equations : sig
      module Scope : sig
        (** [t] represents the "scope" of the equation. It is used to track 
            consistency in level-based generalization *)
        type t = int

        val outermost_scope : t
      end

      module Ctx : sig
        (** [t] represents the equational scope used for Ambivalence *)
        type t

        (** [empty] is the empty equational context. *)
        val empty : t

        exception Inconsistent

        (** [add t type1 type2 scope] adds the equation [type1 = type2] 
            in the scope [scope]. *)
        val add : t -> Rigid_type.t -> Rigid_type.t -> Scope.t -> t
      end
    end

    (** ['a t] represents an ambivalent structure w/ children of type ['a]. *)
    type 'a t

    (** [make_rigid_var rigid_var] returns an ambivalent structure representing 
        the rigid variable [rigid_var] *)
    val make_rigid_var : Rigid_var.t -> 'a t

    (** [make_structure structure] returns an ambivalent structure representing
        [structure]. 
        
        In comparison to [First_order], [None] is equivalent to a flexible variable,
        and [Some structure] is equivalent to the structure [structure]. 
    *)
    val make_structure : 'a S.t option -> 'a t

    (** [make_copy t ~copy] returns a copy of the structure, recursively mapping [copy]. *)
    val make_copy : 'a t -> copy:('a -> 'b) -> 'b t

    (** [structure t] returns the structure of the ambivalent structure. *)
    val structure : 'a t -> 'a S.t option

    (** [scope t] returns the scope of the ambivalent structure. *)
    val scope : 'a t -> Equations.Scope.t

    (** [rigid_vars t] returns the set of ambivalent rigid variables in the structure [t]. *)
    val rigid_vars : 'a t -> Rigid_var.t Hash_set.t

    (** [update_scope t scope] returns [t] with an updated scope. If [scope t < scope], 
        then [t] has the new scope [scope]. *)
    val update_scope : 'a t -> Equations.Scope.t -> 'a t

    (** ['a repr] encodes the "structure" of the Ambivalent. *)
    type 'a repr = 
      | Rigid_var of Rigid_var.t
      | Flexible_var
      | Structure of 'a S.t

    (** [repr t] returns the representation of [t]. *)
    val repr : 'a t -> 'a repr

    type 'a expansive = { make : 'a t -> 'a; sexpansive : 'a S.expansive }

    include S with type 'a t := 'a t and type ctx = Equations.Ctx.t * S.ctx and type 'a expansive := 'a expansive
  end
end