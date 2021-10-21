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

(* [Ast_types] defines auxiliary AST types used by both [Parsetree] 
    and [Typedtree]. *)

type constant = 
  | Const_int of int
  | Const_bool of bool
  | Const_unit 

type primitive = 
  | Prim_add
  | Prim_sub
  | Prim_div
  | Prim_mul

type rec_flag = Nonrecursive | Recursive

