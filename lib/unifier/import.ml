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
include Logs

let src = Logs.Src.create "unifier" ~doc:"logs unifier events"

module Log = (val Logs.src_log src : Logs.LOG)

let reporter =
  let open Stdlib in
  let report _src level' ~over k msgf =
    let k _ =
      over ();
      k ()
    in
    let with_header h fmt =
      (Format.kfprintf k Format.std_formatter ("%a @[" ^^ fmt ^^ "@]@."))
        Logs.pp_header
        (level', h)
    in
    msgf (fun ?header ?tags:_ fmt -> with_header header fmt)
  in
  { Logs.report }


let init_logs ~level:level_ =
  Logs.set_reporter reporter;
  Logs.(
    Src.set_level
      src
      (match level_ with
       | `Debug -> Some Debug
       | `Info -> Some Info
       | `None -> None))
