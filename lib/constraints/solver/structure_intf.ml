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

module type Identifiable = sig
  type 'a t

  val id : 'a t -> int
end

module type S = sig
  (** A structure define the internal structure of unification (or graphical)
      types.
      
      A structures consists of 2 non-separable components: 
      "metadata" and a "descriptor".
      
      Descriptors define the syntactic structure -- often containing children
      of type ['a]. 
      
      Examples of structures include:
        - First order structures
        - First order rows
        - Ambivalent structures      
  *)

  type 'a t [@@deriving sexp_of]

  (** Structures must exhibit [merge] for unification -- this is required for 
      equating structures.  
      
      Equivalence is determined via the ability to emit first-order equalities,
      provided by [equate].

      In some cases, equivalence of 2 structures requires a context. 
      (e.g. Abbreviations, and Ambivalence), thus [merge] requires a context 
      ['a ctx]. 
  *)

  (** ['a ctx] represents the arbitrary context used by [merge] *)
  type 'a ctx

  (** [Cannot_merge] is raised by [merge] -- if the 2 structures are not "consistent". *)
  exception Cannot_merge

  val merge : ctx:'a ctx -> equate:('a -> 'a -> unit) -> 'a t -> 'a t -> 'a t

  (** [map t ~f] traverses [t], applying the transformation [f]. *)
  val map : 'a t -> f:('a -> 'b) -> 'b t

  (** [iter t ~f] traverses [t], executing [f] on each child. *)
  val iter : 'a t -> f:('a -> unit) -> unit

  (** [fold t ~f ~init] performs the computation of [f], traversing
      over [t] with the initial accumulator value of [init]. *)
  val fold : 'a t -> f:('a -> 'b -> 'b) -> init:'b -> 'b
end

module type Intf = sig
  module type S = S

  module Rigid_var : sig
    type t = private int [@@deriving sexp_of, compare]

    val make : unit -> t
    val hash : t -> int
  end

  module Of_former (Former : Type_former.S) : sig
    include S with type 'a t = 'a Former.t and type 'a ctx = unit
  end

  module First_order (S : S) : sig
    type 'a t =
      | Var
      | Structure of 'a S.t

    include S with type 'a t := 'a t and type 'a ctx = 'a S.ctx
  end

  module Ambivalent (S : S) : sig
    module Rigid_type : sig
      type t [@@deriving sexp_of]

      val make_var : unit -> t
      val make_rigid_var : Rigid_var.t -> t
      val make_structure : t S.t -> t
    end

    module Equations : sig
      module Scope : sig
        (** [t] represents the "scope" of the equation. It is used to track 
            consistency in level-based generalization *)
        type t = int

        val outermost_scope : t

        val max : t -> t -> t
      end

      module Ctx : sig
        (** [t] represents the equational scope used for Ambivalence *)
        type t

        (** [empty] is the empty equational context. *)
        val empty : t

        exception Inconsistent

        (** [add t type1 type2 scope] adds the equation [type1 = type2] 
            in the scope [scope]. *)
        val add
          :  ctx:Rigid_type.t S.ctx
          -> t
          -> Rigid_type.t
          -> Rigid_type.t
          -> Scope.t
          -> t
      end
    end

    (** ['a t] represents an ambivalent structure. *)
    type 'a t

    (** ['a repr] is the representation of ['a t]. *)
    type 'a repr =
      | Rigid_var of Rigid_var.t
      | Structure of 'a S.t

    (** [make repr] creates an ambivalent structure with representation [repr]. *)
    val make : 'a repr -> 'a t

    (** [repr t] returns the representation of [t]. *)
    val repr : 'a t -> 'a repr

    (** [scope t] returns the equational scope of [t]. *)
    val scope : 'a t -> Equations.Scope.t

    (** [update_scope t scope] updates the scope of [t]. *)
    val update_scope : 'a t -> Equations.Scope.t -> unit

    type 'a ctx =
      { equations_ctx : Equations.Ctx.t
      ; make : 'a t -> 'a
      ; super_ : 'a S.ctx
      }

    include S with type 'a t := 'a t and type 'a ctx := 'a ctx
  end

  module Abbreviations (S : S) (Id : Identifiable with type 'a t := 'a S.t) : sig
    module Abbrev : sig
      module Type : sig
        type t [@@deriving sexp_of, compare]

        val make_var : unit -> t
        val make_structure : t S.t -> t
      end

      type t

      val make : Type.t S.t -> Type.t -> t

      module Ctx : sig
        type abbrev := t
        type t

        val empty : t
        val add : t -> abbrev:abbrev -> t
      end
    end

    type 'a t

    val make : 'a S.t -> 'a t
    val repr : 'a t -> 'a S.t

    type 'a ctx =
      { abbrev_ctx : Abbrev.Ctx.t
      ; make_structure : 'a S.t -> 'a
      ; make_var : unit -> 'a
      ; super_ : 'a S.ctx
      }

    include S with type 'a t := 'a t and type 'a ctx := 'a ctx
  end

  module Rows (Label : Comparable.S) (S : S) : sig
    type 'a t =
      | Structure of 'a S.t
      | Row_cons of Label.t * 'a * 'a
      | Row_uniform of 'a

    type 'a ctx =
      { make_var : unit -> 'a
      ; make_structure : 'a t -> 'a
      ; super_ : 'a S.ctx
      }

    include S with type 'a t := 'a t and type 'a ctx := 'a ctx
  end
end