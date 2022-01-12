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

  (** [solve t] solves [t] and computes it's value. *)

  type error =
    [ `Unify of Type.t * Type.t
    | `Cycle of Type.t
    | `Unbound_term_variable of Term_var.t
    | `Unbound_constraint_variable of Constraint.variable
    | `Rigid_variable_escape
    ]

  val solve : 'a Constraint.t -> ('a, [> error ]) Result.t
end

(** [Private] submodule for [expect] tests. *)
module Private : sig
  module Generalization (Type_former : Type_former.S) :
    Generalization.S with type 'a former := 'a Type_former.t

  module Unifier (Type_former : Type_former.S) (Metadata : Unifier.Metadata) :
    Unifier.S
      with type 'a former := 'a Type_former.t
       and type metadata := Metadata.t

  module Union_find : module type of Union_find
end
