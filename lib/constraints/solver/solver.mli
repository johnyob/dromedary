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
  module Label := Types.Label
  module Type_var := Types.Var
  module Type_former := Types.Former

  module Decoded :
    Decoded
      with type label := Types.Label.t
       and type 'a former := 'a Types.Former.t

  module Algebra_with_decoded :
    Algebra_with_decoded
      with module Term_var = Term_var
       and module Types = Types
       and module Decoded = Decoded

  module Constraint := Constraint.Make(Algebra_with_decoded)

  module Abbrev_type : sig
    type t [@@deriving sexp_of, compare]

    val make_var : unit -> t
    val make_former : t Type_former.t -> t
  end

  module Abbreviations : sig
    type t

    val empty : t
    val add : t -> abbrev:Abbrev_type.t Type_former.t * Abbrev_type.t -> t
  end

  (** [solve t] solves [t] and computes it's value. *)

  type error =
    [ `Unify of Decoded.Type.t * Decoded.Type.t
    | `Cycle of Decoded.Type.t
    | `Unbound_term_variable of Term_var.t
    | `Unbound_constraint_variable of Constraint.variable
    | `Rigid_variable_escape of Type_var.t
    | `Cannot_flexize of Type_var.t
    | `Scope_escape of Decoded.Type.t
    | `Non_rigid_equations
    | `Inconsistent_equations
    ]

  val solve
    :  ?debug:bool
    -> abbrevs:Abbreviations.t
    -> 'a Constraint.t
    -> ('a, [> error ]) Result.t

  module Structure : sig
    val solve
      :  ?debug:bool
      -> abbrevs:Abbreviations.t
      -> 'a Constraint.Structure.t
      -> ('a list, [> error ]) Result.t
  end
end

(** [Private] submodule for [expect] tests. *)
module Private : sig
  module Structure = Structure

  module Generalization (Label : Comparable.S) (Type_former : Type_former.S) :
    Generalization.S
      with type 'a former := 'a Type_former.t
       and type label := Label.t
end
