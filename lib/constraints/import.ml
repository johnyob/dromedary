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


include Base
module Format = Stdlib.Format

module Unifier = Dromedary_lib_unifier

include Logs

let src =
  Logs.Src.create "constraints.solver" ~doc:"logs constraint solver events"


let reporter =
  let report _src level' ~over k msgf =
    let k _ =
      over ();
      k ()
    in
    let with_header h fmt =
      Stdlib.(Format.kfprintf k Format.std_formatter ("%a @[" ^^ fmt ^^ "@]@."))
        Logs.pp_header
        (level', h)
    in
    msgf (fun ?header ?tags:_ fmt -> with_header header fmt)
  in
  { Logs.report = report }


module Log = (val Logs.src_log src : Logs.LOG)

(* See: https://github.com/janestreet/base/issues/121 *)
let post_incr r =
  let result = !r in
  Int.incr r;
  result

module Constraint = Constraint
include Constraint.Module_types
