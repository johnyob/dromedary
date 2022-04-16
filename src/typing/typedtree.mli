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
open Parsing.Ast_types
open Types

type 'a instance = 'a * type_expr list [@@deriving sexp_of]

and 'a abstraction = type_var list * 'a [@@deriving sexp_of]

type pattern =
  { pat_desc : pattern_desc
  ; pat_type : type_expr
  }
[@@deriving sexp_of]

and pattern_desc =
  | Tpat_any
      (** [_] *)
  | Tpat_var of string
      (** [x] *)
  | Tpat_alias of pattern * string
      (** [P as x] *)
  | Tpat_const of constant
      (** [c] e.g. [1, true, ()] *)
  | Tpat_tuple of pattern list
      (** [(P1, ..., Pn)]. Invariant n >= 2 *)
  | Tpat_construct of constructor_description * pattern option
      (** [C <P>] *)
  | Tpat_variant of variant_description * pattern option
      (** [`A <P>] *)
[@@deriving sexp_of]

val pp_pattern_mach : pattern Pretty_printer.t
val pp_pattern : pattern Pretty_printer.t

type expression =
  { exp_desc : expression_desc
  ; exp_type : type_expr
  }
[@@deriving sexp_of]

and expression_desc =
  | Texp_var of string instance 
      (** [x]. *)
  | Texp_prim of primitive
      (** Primitive operations [%prim p]. e.g. [%prim +], [%prim -], etc. *)
  | Texp_const of constant 
      (** Constants [c]. e.g. [1, true, ()]. *)
  | Texp_fun of pattern * expression
      (** The function (or lambda) abstraction [fun P -> E].  
          Note that: 
            - [let x P1 ... Pn = E in ...] is encoding using 
              [Texp_let ("x", fun P1 ... Pn -> E, ...)]. 
      *)
  | Texp_app of expression * expression 
      (** Function application [E1 E2]. *)
  | Texp_let of value_binding list * expression 
      (** Let expressions *)
  | Texp_let_rec of rec_value_binding list * expression
      (** Let rec expressions *)
  | Texp_construct of constructor_description * expression option
      (** An applied algebraic data type constructor [C <E>]. *)
  | Texp_record of (label_description * expression) list
      (** [{l1 = E1; ...; ln = En}] *)
  | Texp_field of expression * label_description 
      (** [E.l] *)
  | Texp_tuple of expression list
      (** Tuples [(E1, ..., En)]. Invariant: n >= 2. *)
  | Texp_match of expression * type_expr * case list
      (** Match (or "case") expressions [match E with (P1 -> E1 | ... | Pn -> En)]. *)
  | Texp_ifthenelse of expression * expression * expression
      (** If (or ternary) expressions [if E then E1 else E2]. *)
  | Texp_try of expression * case list
      (** [try E0 with P1 -> E1 | ... | Pn -> En] *)
  | Texp_sequence of expression * expression
      (** [E1; E2] *)
  | Texp_while of expression * expression
      (** [while E1 do E2 done] *)
  | Texp_for of string * expression * expression * direction_flag * expression
      (** [for i = E1 to E2 do E3 done]
          [for i = E2 downto E2 do E3 done] *)
  | Texp_variant of variant_description * expression option
      (** Polymorphic variant [`A <E>]. *)
[@@deriving sexp_of]

(** [P = a .. a. E]. *)
and value_binding =
  { tvb_pat : pattern
  ; tvb_expr : expression abstraction
  }
[@@deriving sexp_of]

(** [x = a .. a. E] *)
and rec_value_binding =
  { trvb_var : string
  ; trvb_expr : expression abstraction
  }
[@@deriving sexp_of]

(** [P -> E]. *)
and case =
  { tc_lhs : pattern
  ; tc_rhs : expression
  }
[@@deriving sexp_of]

val pp_expression_mach : expression Pretty_printer.t
val pp_expression : expression Pretty_printer.t
val pp_value_binding_mach : value_binding Pretty_printer.t
val pp_value_binding : value_binding Pretty_printer.t
val pp_rec_value_binding_mach : rec_value_binding Pretty_printer.t
val pp_rec_value_binding : rec_value_binding Pretty_printer.t
val pp_case_mach : case Pretty_printer.t
val pp_case : case Pretty_printer.t

type value_description = 
  { tval_name : string
  ; tval_type : scheme
  ; tval_prim : string
  }
[@@deriving sexp_of]

type extension_constructor = 
  { text_name : string
      (** Extension type name [t]. *)
  ; text_params : type_var list
      (** Extension type params: [('a1, ..., 'an)]. *)
  ; text_kind : extension_constructor_kind 
  }
[@@derving sexp_of]

and extension_constructor_kind = 
  | Text_decl of constructor_declaration
      (** [C of 'b1 .. 'bm. T constraint E] *)
[@@derving sexp_of]

(** Exception [exception C <of T>] *)
type type_exception = 
  { tyexn_constructor : extension_constructor }
[@@derving sexp_of]

type structure_item = 
  | Tstr_value of value_binding list 
    (** Let expressions *)
  | Tstr_value_rec of rec_value_binding list
    (** Let rec expressions *)
  | Tstr_primitive of value_description
      (** External primitive descriptions *)
  | Tstr_type of type_declaration list
      (** Type declarations [type t1 = ... and ... tn = ...] *)
  | Tstr_exception of type_exception
      (** Exception [exception C <of T>] *)
[@@deriving sexp_of]

type structure = structure_item list [@@deriving sexp_of]

val pp_structure_mach : structure Pretty_printer.t


