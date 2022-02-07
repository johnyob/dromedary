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

  module Abbrev_type : sig
    type t [@@deriving sexp_of, compare]

    val make_var : unit -> t
    val make_former : t Type_former.t -> t
  end


  module Abbreviations : sig
    type t

    val empty : t
    val add : t -> abbrev:(Abbrev_type.t Type_former.t * Abbrev_type.t) -> t
  end

  (** [solve t] solves [t] and computes it's value. *)

  type error =
    [ `Unify of Type.t * Type.t
    | `Cycle of Type.t
    | `Unbound_term_variable of Term_var.t
    | `Unbound_constraint_variable of Constraint.variable
    | `Rigid_variable_escape of Type_var.t
    | `Cannot_flexize of Type_var.t
    | `Scope_escape of Type.t
    | `Non_rigid_equations
    | `Inconsistent_equations
    ]

  val solve : ?debug:bool -> abbrevs:Abbreviations.t -> 'a Constraint.t -> ('a, [> error ]) Result.t
end

(** [Private] submodule for [expect] tests. *)
module Private : sig
  module Structure = Structure

  module Generalization (Type_former : Type_former.S) :
    Generalization.S with type 'a former := 'a Type_former.t

  module Unifier (Structure : Structure.S) :
    Unifier.S
      with type 'a structure = 'a Structure.t
       and type 'a metadata = 'a Structure.Metadata.t
       and type ctx = Structure.ctx
       and type 'a expansive = 'a Structure.expansive

  module Union_find : module type of Union_find
end
