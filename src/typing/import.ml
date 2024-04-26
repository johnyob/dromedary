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

module Parsing_ = Parsing (* Core overwrites [Parsing] *)
include Core

(* Include other libraries *)
include Parsing_
include Algebra
module Constraint = Constraints.Make (Algebra)

module Decoded = Constraint.Decoded