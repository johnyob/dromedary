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

open! Import

module Make (Algebra : Algebra) : sig
  open Algebra
  module Type_var := Types.Var
  module Type := Types.Type
  module Type_former := Types.Former
  module Constraint := Constraint.Make(Algebra)

  module Abbreviations : sig
    module Abbrev_type : sig
      (** [t] represents a graphical encoding of an abbreviational type *)
      type t [@@deriving sexp_of, compare]

      type structure =
        | Var
        | Former of t Type_former.t

      (** [make_var ()] returns a fresh abbreviation type variable. *)
      val make_var : unit -> t

      (** [make_former former] returns a fresh abbreviation former for [former]. *)
      val make_former : t Type_former.t -> t
    end

    module Abbreviation : sig
      type t

      val make
        :  former:_ Type_former.t
        -> rank:int
        -> decomposable_positions:int list
        -> productivity:
             [ `Non_productive of int
             | `Productive of Abbrev_type.t Type_former.t
             ]
        -> type_:Abbrev_type.t list * Abbrev_type.t Type_former.t
        -> t
    end

    module Ctx : sig
      type t

      val empty : t
      val add : t -> abbrev:Abbreviation.t -> t
    end
  end

  (** [solve t] solves [t] and computes it's value. *)

  type error =
    [ `Unify of Type.t * Type.t
    | `Cycle of Type.t
    | `Unbound_term_variable of Term_var.t
    | `Unbound_constraint_variable of Constraint.variable
    | `Rigid_variable_escape of Type_var.t
    | `Cannot_flexize of Type_var.t
    ]

  val solve
    :  ctx:Abbreviations.Ctx.t
    -> 'a Constraint.t
    -> ('a, [> error ]) Result.t
end

(** [Private] submodule for [expect] tests. *)
module Private : sig
  module Generalization (Type_former : Type_former.S) :
    Generalization.S with type 'a former := 'a Type_former.t

  module Unifier (Former : Unifier.Former) (Metadata : Unifier.Metadata.S1) :
    Unifier.S
      with type 'a former := 'a Former.t
       and type 'a ctx := 'a Former.Ctx.t
       and type 'a metadata := 'a Metadata.t

  module Union_find : module type of Union_find
end
