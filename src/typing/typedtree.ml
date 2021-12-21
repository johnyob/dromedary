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

open Parsing
open Ast_types
open Types

(** Abstract syntax tree after typing *)

type 'a instance = 'a * type_expr list

and 'a abstraction = string list * 'a

type pattern =
  { pat_desc : pattern_desc
  ; pat_type : type_expr
  }

and pattern_desc =
  | Tpat_any (** [_] *)
  | Tpat_var of string (** [x]. *)
  | Tpat_alias of pattern * string (** [P as x]. *)
  | Tpat_const of constant (** [c]. e.g. [1, true, ()]. *)
  | Tpat_tuple of pattern list (** (P1, ..., Pn). Invariant n >= 2. *)
  | Tpat_construct of constructor_description * pattern option (** [C <P>]. *)

type expression =
  { exp_desc : expression_desc
  ; exp_type : type_expr
  }

and expression_desc =
  | Texp_var of string instance (** [x]. *)
  | Texp_prim of primitive
      (** Primitive operations [%prim p]. e.g. [%prim +], [%prim -], etc. *)
  | Texp_const of constant (** Constants [c]. e.g. [1, true, ()]. *)
  | Texp_fun of pattern * expression
      (** The function (or lambda) abstraction [fun P -> E].  
          Note that: 
            - [let x P1 ... Pn = E in ...] is encoding using 
              [Pexp_let ("x", fun P1 ... Pn -> E, ...)]. 
      *)
  | Texp_app of expression * expression (** Function application [E1 E2]. *)
  | Texp_let of value_binding list * expression (** Let expressions *)
  | Texp_let_rec of rec_value_binding list * expression
  | Texp_construct of constructor_description * expression option
      (** An applied algebraic data type constructor [C <E>]. *)
  | Texp_record of (label_description * expression) list
      (** {l1 = E1; ...; ln = En} *)
  | Texp_field of expression * label_description (** E.l *)
  | Texp_tuple of expression list
      (** Tuples [(E1, ..., En)]. Invariant: n >= 2. *)
  | Texp_match of expression * type_expr * case list
      (** Match (or "case") expressions [match E with (P1 -> E1 | ... | Pn -> En)]. *)
  | Texp_ifthenelse of expression * expression * expression
      (** If (or ternary) expressions [if E then E1 else E2]. *)

(** [P = a .. a. E]. *)
and value_binding =
  { tvb_pat : pattern
  ; tvb_expr : expression abstraction
  }

(** [x = a .. a. E] *)
and rec_value_binding =
  { trvb_var : string
  ; trvb_expr : expression abstraction
  }

(** [P -> E]. *)
and case =
  { tc_lhs : pattern
  ; tc_rhs : expression
  }
