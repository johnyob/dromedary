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
  include Private.Constraint.Make (Algebra)

  module Rigid = struct
    let rec to_constraint t =
      match t with
      | Rigid.True -> True
      | Rigid.Conj ts -> List.map ~f:to_constraint ts |> all_unit
      | Rigid.Eq (t1, t2) ->
        let bindings1, t1 = Shallow_type.of_type t1 in
        let bindings2, t2 = Shallow_type.of_type t2 in
        exists (bindings1 @ bindings2) (t1 =~ t2)


    include Rigid
  end

  module Solver = Private.Solver.Make (Algebra)

  let solve = Solver.solve
end

module Private = struct
  module Constraint = Private.Constraint
  include Private.Solver.Private
end
