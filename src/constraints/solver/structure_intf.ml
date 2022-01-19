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
  type 'a t

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
      
      In some cases, consistency may also fold and unfold the fixed point, 
      used by the unifier (e.g. Rows, Abbreviations and Ambivalence). This
      is provided by the parameter [term].
  *)

  type term = { fold : 'a. 'a t -> 'a }
  type ctx

  exception Cannot_merge

  val merge
    :  term:term
    -> ctx:ctx
    -> equate:('a -> 'a -> unit)
    -> 'a t
    -> 'a t
    -> 'a t
end

module type Intf = sig
  module type S = S

  module Rigid_var : sig
    type t = private int [@@deriving compare]

    val make : unit -> t
    val hash : t -> int
  end

  module First_order (S : S) : sig
    type 'a t =
      | Var
      | Structure of 'a S.t

    include S with type 'a t := 'a t
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

    type 'a t

    val make_rigid_var : Rigid_var.t -> 'a t
    val make_structure : 'a S.t option -> 'a t
    val structure : 'a t -> 'a S.t option
    val scope : 'a t -> Equations.Scope.t

    type ctx = Equations.Ctx.t * S.ctx

    include S with type 'a t := 'a t and type ctx := ctx
  end
end