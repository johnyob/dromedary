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

open Constraints.Module_types

module Term_var : Term_var with type t = string

module Type_var : Type_var with type t = string

module Type_former : sig
  type 'a t =
    | Arrow of 'a * 'a
    | Tuple of 'a list
    | Constr of 'a list * string

  include Type_former with type 'a t := 'a t
end

module Type :
  Type
    with type variable := Type_var.t
     and type 'a former := 'a Type_former.t

module Algebra : Algebra
