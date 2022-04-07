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
open Constraint

type variant_pattern = Vpat_variant of string * Parsetree.pattern option

val variant_pattern_of_pattern : Parsetree.pattern -> variant_pattern option

type variant_cases

val variant_cases_of_cases : Parsetree.case list -> variant_cases option
val infer_constant : Ast_types.constant -> Type.t

module Pattern : sig
  module Computation = Computation.Pattern

  val infer_pat
    :  Parsetree.pattern
    -> variable
    -> Typedtree.pattern Constraint.t Computation.t
end

module Expression : sig
  module Computation = Computation.Expression
  open Computation

  val infer_primitive : Ast_types.primitive -> Type.t Binder.t

  val infer_exp
    :  Parsetree.expression
    -> variable
    -> Typedtree.expression Constraint.t Computation.t

  val infer_exp_
    :  Parsetree.expression
    -> Typedtree.expression bound Constraint.t Computation.t

  val infer_value_bindings
    :  Parsetree.value_binding list
    -> (Typedtree.pattern * Typedtree.expression) let_binding list Computation.t

  val infer_rec_value_bindings
    :  Parsetree.value_binding list
    -> Typedtree.expression let_rec_binding list Computation.t

  module Structure : sig
    open Structure.Item

    val infer_value_bindings
      :  Parsetree.value_binding list
      -> (Typedtree.pattern * Typedtree.expression) let_binding list
         Computation.t

    val infer_rec_value_bindings
      :  Parsetree.value_binding list
      -> Typedtree.expression let_rec_binding list Computation.t
  end
end