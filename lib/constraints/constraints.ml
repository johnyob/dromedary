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
module Module_types = Private.Constraint.Module_types

module Make (Algebra : Algebra) = struct
  module Solver = Private.Solver.Make (Algebra)

  module Decoded = Solver.Decoded
  include Private.Constraint.Make (Solver.Algebra_with_decoded)


  module Abbrev_type = Solver.Abbrev_type
  module Abbreviations = Solver.Abbreviations

  let solve = Solver.solve

  module Structure = struct
    include Structure
    let solve = Solver.Structure.solve
  end
end

module Private = struct
  module Constraint = Private.Constraint
  include Private.Solver.Private
end
