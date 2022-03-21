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
  | Const_float of float
  | Const_bool of bool
  | Const_char of char
  | Const_string of string
  | Const_unit
[@@deriving sexp_of]

let string_of_constant constant =
  match constant with
  | Const_int n -> Format.asprintf "%d" n
  | Const_float f -> Format.asprintf "%f" f
  | Const_bool b -> Format.asprintf "%b" b
  | Const_char c -> Format.asprintf "%c" c
  | Const_string s -> s
  | Const_unit -> "()"


type primitive =
  | Prim_add
  | Prim_sub
  | Prim_div
  | Prim_mul
  | Prim_eq
  | Prim_ref
  | Prim_deref
  | Prim_assign
[@@deriving sexp_of]

let string_of_primitive primitive =
  match primitive with
  | Prim_add -> "(+)"
  | Prim_sub -> "(-)"
  | Prim_div -> "(/)"
  | Prim_mul -> "(*)"
  | Prim_eq -> "(=)"
  | Prim_ref -> "ref"
  | Prim_deref -> "(!)"
  | Prim_assign -> "(:=)"


type rec_flag =
  | Nonrecursive
  | Recursive
[@@deriving sexp_of]

let string_of_rec_flag rec_flag =
  match rec_flag with
  | Nonrecursive -> "Nonrecursive"
  | Recursive -> "Recursive"


type direction_flag =
  | Upto
  | Downto
[@@deriving sexp_of]

let string_of_direction_flag direction_flag =
  match direction_flag with
  | Upto -> "to"
  | Downto -> "downto"


