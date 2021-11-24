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

(* ------------------------------------------------------------------------- *)

(** Natural numbers *)

(* The type [z] encodes the natural number zero. *)
type z = Z

(* The type ['n s] encodes the successor of ['n]. *)
type 'n s = S

(* ------------------------------------------------------------------------- *)

(** A size is used to index sized types, e.g. the length of a list.

    We do this statically, using "phantom types". Here the phantom type
    ['n] corresponds to the natural number of the size, namely:
      - zero, or
      - suc 'm. *)
type 'n t = 
  | Zero : z t
  | Suc  : 'n t -> 'n s t 

(* ------------------------------------------------------------------------- *)

(** Constants *)

type one = z s

let one = Suc Zero

type two = one s

let two = Suc one

type three = two s

let three = Suc two

type four = three s

let four = Suc three

type five = four s

let five = Suc four

type six = five s

let six = Suc five

type seven = six s

let seven = Suc six

type eight = seven s

let eight = Suc seven

type nine = eight s

let nine = Suc eight

type ten = nine s

let ten = Suc nine
