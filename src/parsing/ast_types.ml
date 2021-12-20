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

open Core

(* [Ast_types] defines auxiliary AST types used by both [Parsetree] 
    and [Typedtree]. *)

type constant =
  | Const_int of int
  | Const_bool of bool
  | Const_unit
[@@deriving sexp_of]

let string_of_constant constant =
  match constant with
  | Const_int n -> Format.asprintf "Int: %d" n
  | Const_bool b -> Format.asprintf "Bool: %b" b
  | Const_unit -> "Unit"


type primitive =
  | Prim_add
  | Prim_sub
  | Prim_div
  | Prim_mul
[@@deriving sexp_of]

let string_of_primitive primitive =
  match primitive with
  | Prim_add -> "(+)"
  | Prim_sub -> "(-)"
  | Prim_div -> "(/)"
  | Prim_mul -> "(*)"


type non_rec
type rec_

type 'a rec_flag =
  | Nonrecursive : non_rec rec_flag
  | Recursive : rec_ rec_flag
[@@deriving sexp_of]

let string_of_rec_flag : type a. a rec_flag -> string =
 fun rec_flag ->
  match rec_flag with
  | Nonrecursive -> "Nonrecursive"
  | Recursive -> "Recursive"