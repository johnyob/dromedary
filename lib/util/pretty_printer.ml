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

let none : separator = ""

let paren ?(first = none) ?(last = none) ~parens (pp : 'a t) : 'a t =
 fun ppf t ->
  if parens
  then (
    Format.fprintf ppf "(";
    Format.fprintf ppf first;
    pp ppf t;
    Format.fprintf ppf last;
    Format.fprintf ppf ")")
  else pp ppf t


let list ?(sep = ("@ " : separator)) ?(first = none) ?(last = none) (pp : 'a t)
    : 'a list t
  =
 fun ppf ts ->
  match ts with
  | [] -> ()
  | [ t ] -> pp ppf t
  | ts ->
    let rec loop ppf ts =
      match ts with
      | [] -> assert false
      | [ t ] -> pp ppf t
      | t :: ts ->
        pp ppf t;
        Format.fprintf ppf sep;
        loop ppf ts
    in
    Format.fprintf ppf first;
    loop ppf ts;
    Format.fprintf ppf last


let option ?(first = none) ?(last = none) (pp : 'a t) : 'a option t =
 fun ppf opt ->
  match opt with
  | None -> ()
  | Some t ->
    Format.fprintf ppf first;
    pp ppf t;
    Format.fprintf ppf last
