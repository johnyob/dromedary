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

open Ast_types

(** [Parsetree] is the abstract syntax tree produced by parsing
    Dromedary's source code. *)

(** ['a pp] is the type of a pretty printer for type ['a]. *)
type 'a pp = Format.formatter -> 'a -> unit

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

(** [pp_core_type_mach ppf core_type] pretty prints [core_type] in a "machine format" (an explicit tree structure). *)
val pp_core_type_mach : core_type pp

(** [pp_core_type ppf core_type] pretty prints [core_type] as a syntactic representation. *)
val pp_core_type : core_type pp

(** [core_schemes] are defined by the grammar: 
    core_schemes ::= 'a1 ... 'an. T 
    
    This "source"-level notion of type schemes is often used
    in annotations in [expression] and [pattern]. 
*)
type core_scheme = string list * core_type [@@deriving sexp_of]

val pp_core_scheme_mach : core_scheme pp
val pp_core_scheme : core_scheme pp

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
  | Ppat_construct of string * pattern option 
      (** [C <P>]. *)
  | Ppat_constraint of pattern * core_type 
      (** [(P : T)]. *)
[@@deriving sexp_of]

val pp_pattern_mach : pattern pp
val pp_pattern : pattern pp

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
  | Pexp_let of value_bindings * expression
      (** Let expressions:
          [let P1 = E1 and ... and Pn = En in E]      ([value_bindings = Nonrecursive ...]).    
          [let rec P1 = E1 and ... Pn = En in E]      ([value_bindings = Recursive ...]). 
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
[@@deriving sexp_of]

and value_bindings =
  | Recursive of rec_value_binding list
  | Nonrecursive of nonrec_value_binding list
[@@deriving sexp_of]

(** [P = E]. *)
and nonrec_value_binding =
  { pnvb_pat : pattern
  ; pnvb_expr : expression
  }
[@@deriving sexp_of]

(** [x = E] *)
and rec_value_binding =
  { prvb_var : string
  ; prvb_expr : expression
  }
[@@deriving sexp_of]

(** [P -> E]. *)
and case =
  { pc_lhs : pattern
  ; pc_rhs : expression
  }
[@@deriving sexp_of]

(** [pp_expression_mach ppf exp] pretty prints an expression [exp] as an explicit tree structure. *)
val pp_expression_mach : expression pp

(** [pp_expression ppf exp] pretty prints an expression [exp] as a syntax representation. *)
val pp_expression : expression pp

(** [pp_value_bindings_mach ppf value_bindings] pretty prints the value bindings [value_bindings] as 
    an explicit tree of bindings. *)
val pp_value_bindings_mach : value_bindings pp

(** [pp_value_bindings ppf value_bindings] pretty prints the value bindings [value_bindings] as a 
    syntactic representation, using [and] as a separator. *)
val pp_value_bindings : value_bindings pp

(** [pp_nonrec_value_binding_mach ppf nonrec_value_binding] pretty prints the non recursive value binding
    [nonrec_value_binding], using an explicit tree structure. *)
val pp_nonrec_value_binding_mach : nonrec_value_binding pp

(** [pp_nonrec_value_binding ppf nonrec_value_binding] pretty prints the non recursive value binding
    [nonrec_value_binding] as a syntactic representation. *)
val pp_nonrec_value_binding : nonrec_value_binding pp

(** [pp_rec_value_binding_mach ppf rec_value_binding] pretty prints the recursive value binding
    [rec_value_binding], using an explicit tree structure. *)
val pp_rec_value_binding_mach : rec_value_binding pp

(** [pp_rec_value_binding ppf rec_value_binding] pretty prints the recursive value binding
    [rec_value_binding] as a syntactic representation. *)
val pp_rec_value_binding : rec_value_binding pp

(** [pp_case_mach ppf case] pretty prints the case [case] as an explicit tree structure. *)
val pp_case_mach : case pp

(** [pp_case ppf case] prety prints the case [case] as a syntactic representation. *)
val pp_case : case pp
