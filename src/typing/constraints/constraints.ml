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

module Make (Algebra : Algebra) = struct

  module Constraint = Constraint.Make (Algebra)

  module Computation = struct
    module type Basic = Computation.Basic
    module type Basic2 = Computation.Basic2

    module type S = Computation.S
    module type S2 = Computation.S2

    module Make (Basic : Basic) = Computation.Make (Algebra) (Basic)

    module Make2 (Basic : Basic2) = Computation.Make2 (Algebra) (Basic)
  end

end