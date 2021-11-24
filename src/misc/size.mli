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

val one : one t

type two = one s

val two : two t

type three = two s

val three : three t

type four = three s

val four : four t

type five = four s

val five : five t

type six = five s

val six : six t

type seven = six s

val seven : seven t

type eight = seven s

val eight : eight t

type nine = eight s

val nine : nine t

type ten = nine s

val ten : ten t


