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

type 'a t = Format.formatter -> 'a -> unit
type separator = (unit, Format.formatter, unit) format

val paren : ?first:separator -> ?last:separator -> parens:bool -> 'a t -> 'a t

val list
  :  ?sep:separator
  -> ?first:separator
  -> ?last:separator
  -> 'a t
  -> 'a list t

val option : ?first:separator -> ?last:separator -> 'a t -> 'a option t
