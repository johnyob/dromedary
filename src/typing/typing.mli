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
module Types = Types
module Typedtree = Typedtree
module Env = Env

val infer_exp
  :  ?debug:bool
  -> env:Env.t
  -> abbrevs:Abbreviations.t
  -> Parsetree.expression
  -> (Typedtree.expression bound, Sexp.t) Result.t

val infer_str
  :  ?debug:bool
  -> Parsetree.structure
  -> (Typedtree.structure, Sexp.t) Result.t

module Private : sig
  module Constraint = Constraint
  module Computation = Computation
  module Infer_core = Infer_core
  module Algebra = Algebra
  module Infer_structure = Infer_structure

  val solve
    :  ?debug:bool
    -> abbrevs:Abbreviations.t
    -> 'a Constraint.t
    -> ('a, Sexp.t) Result.t
end
