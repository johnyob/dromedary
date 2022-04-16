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

val core_type
  :  substitution:Substitution.t
  -> Parsetree.core_type
  -> (variable list * Type.t, [> `Unbound_type_variable of string ]) Result.t

val row
  :  substitution:Substitution.t
  -> Parsetree.row
  -> (variable list * Type.t, [> `Unbound_type_variable of string ]) Result.t

val type_expr
  :  substitution:variable Types.Type_var.Map.t
  -> Types.type_expr
  -> ( Type.t
     , [> `Unbound_type_variable of Types.type_var
       | `Type_expr_is_ill_sorted of Types.type_expr
       ] )
     Result.t

module With_computation (Computation : Computation.S) : sig
  val core_type : Parsetree.core_type -> (variable list * Type.t) Computation.t
  val row : Parsetree.row -> (variable list * Type.t) Computation.t

  val type_expr
    :  substitution:variable Types.Type_var.Map.t
    -> Types.type_expr
    -> Type.t Computation.t
end