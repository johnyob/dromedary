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

open Util
open Ast_types

(** [Parsetree] is the abstract syntax tree produced by parsing
    Dromedary's source code. *)

type core_type =
  | Ptyp_var of string 
      (** Type variables ['a]. *)
  | Ptyp_arrow of core_type * core_type 
      (** Function types [T1 -> T2]. *)
  | Ptyp_tuple of core_type list 
      (** Product (or "tuple") types. *)
  | Ptyp_constr of core_type list * string
      (** A type constructor (or "type former"), name "constr" is used for 
          consistency between OCaml and Dromedary code. *)
[@@deriving sexp_of]

(** [pp_core_type_mach ppf core_type] pretty prints [core_type] in a "machine format" 
    (an explicit tree structure). *)
val pp_core_type_mach : core_type Pretty_printer.t

(** [pp_core_type ppf core_type] pretty prints [core_type] as a syntactic representation. *)
val pp_core_type : core_type Pretty_printer.t

(** [core_schemes] are defined by the grammar: 
    core_schemes ::= 'a1 ... 'an. T 
    
    This "source"-level notion of type schemes is often used
    in annotations in [expression] and [pattern]. 
*)
type core_scheme = string list * core_type [@@deriving sexp_of]

val pp_core_scheme_mach : core_scheme Pretty_printer.t
val pp_core_scheme : core_scheme Pretty_printer.t

type pattern =
  | Ppat_any 
      (** [_]. *)
  | Ppat_var of string 
      (** [x]. *)
  | Ppat_alias of pattern * string 
      (** [P as x]. *)
  | Ppat_const of constant 
      (** [c]. e.g. [1, true, ()]. *)
  | Ppat_tuple of pattern list 
      (** (P1, ..., Pn). Invariant n >= 2. *)
  | Ppat_construct of string * (string list * pattern) option 
      (** [C <P>]. *)
  | Ppat_constraint of pattern * core_type 
      (** [(P : T)]. *)
[@@deriving sexp_of]

val pp_pattern_mach : pattern Pretty_printer.t
val pp_pattern : pattern Pretty_printer.t

type expression =
  | Pexp_var of string 
      (** [x]. *)
  | Pexp_prim of primitive
      (** Primitive operations [%prim p]. e.g. [%prim +], [%prim -], etc. *)
  | Pexp_const of constant 
      (** Constants [c]. e.g. [1, true, ()]. *)
  | Pexp_fun of pattern * expression
      (** The function (or lambda) abstraction [fun P -> E].  
          Note that: 
            - [let x P1 ... Pn = E in ...] is encoding using 
              [Pexp_let ("x", fun P1 ... Pn -> E, ...)]. 
      *)
  | Pexp_app of expression * expression 
      (** Function application [E1 E2]. *)
  | Pexp_let of rec_flag * value_binding list * expression
      (** Let expressions:
          [let P1 = E1 and ... and Pn = En in E]    
      *)
  | Pexp_forall of string list * expression
      (** Explicit "forall" quantifier [forall 'a1 ... 'an -> E]. 
          Invariant n >= 1. *)
  | Pexp_exists of string list * expression
      (** Explicit "exists" quantifier [exists 'a1 ... 'an -> E]. 
          Invariant n >= 1. *)
  | Pexp_constraint of expression * core_type
      (** An expression "constraint" or typing annotation [(E : T)]. *)
  | Pexp_construct of string * expression option
      (** An applied algebraic data type constructor [C <E>]. *)
  | Pexp_record of (string * expression) list 
      (** {l1 = E1; ...; ln = En} *)
  | Pexp_field of expression * string 
      (** E.l *)
  | Pexp_tuple of expression list
      (** Tuples [(E1, ..., En)]. Invariant: n >= 2. *)
  | Pexp_match of expression * case list
      (** Match (or "case") expressions [match E with (P1 -> E1 | ... | Pn -> En)]. *)
  | Pexp_ifthenelse of expression * expression * expression
      (** If (or ternary) expressions [if E then E1 else E2]. *)
  | Pexp_try of expression * case list
      (** try E0 with P1 -> E1 | ... | Pn -> En *)
  | Pexp_sequence of expression * expression
      (** E1; E2 *)
  | Pexp_while of expression * expression
      (** while E1 do E2 done *)
  | Pexp_for of pattern * expression * expression * direction_flag * expression
      (** for i = E1 to E2 do E3 done
          for i = E2 downto E2 do E3 done *)
[@@deriving sexp_of]

(** [P = E] *)
and value_binding =
  { pvb_forall_vars : string list 
  ; pvb_pat : pattern
  ; pvb_expr : expression
  }
[@@deriving sexp_of]


(** [P -> E]. *)
and case =
  { pc_lhs : pattern
  ; pc_rhs : expression
  }
[@@deriving sexp_of]

(** [pp_expression_mach ppf exp] pretty prints an expression [exp] as an explicit tree structure. *)
val pp_expression_mach : expression Pretty_printer.t

(** [pp_expression ppf exp] pretty prints an expression [exp] as a syntax representation. *)
val pp_expression : expression Pretty_printer.t

(** [pp_value_binding_mach ppf value_binding] pretty prints the value binding [value_binding]
    as an explicit tree. *)
val pp_value_binding_mach : value_binding Pretty_printer.t

(** [pp_value_binding ppf value_binding] pretty prints the value binding [value_bindings] as a 
    syntactic representation. *)
val pp_value_binding : value_binding Pretty_printer.t

(** [pp_case_mach ppf case] pretty prints the case [case] as an explicit tree structure. *)
val pp_case_mach : case Pretty_printer.t

(** [pp_case ppf case] prety prints the case [case] as a syntactic representation. *)
val pp_case : case Pretty_printer.t