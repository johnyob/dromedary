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

open Constraint.Intf

(* ------------------------------------------------------------------------- *)

module Make (Term_var : Term_var) (Types : Types) : sig

  (* Instantiate constraint types. *)

  module Constraint := Constraint.Make(Term_var)(Types)

  (* [solve] takes a ['a Constraint.t], solves it
     and returns it's "value". 
     
     If the constraint is unsolvable (i.e. reduces to Cst_false), 
     then raises an exception. 
     
     TODO: Improve exception interface *)

  val solve : 'a Constraint.t -> 'a
end
