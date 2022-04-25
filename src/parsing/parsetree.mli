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
  | Ptyp_variant of row
      (** Polymorphic variants [ [ ... ] ] *)
  | Ptyp_mu of string * core_type
      (** Equi-recursive types [ mu 'a. T ] *)
  | Ptyp_where of core_type * string * core_type
      (** where-binding [ T where 'a = T ] *)
[@@deriving sexp_of]

and row = row_field list * closed_flag
[@@deriving sexp_of]

and row_field = 
  | Row_tag of string * core_type option
      (** [ `A ]
          [ `A of T ] *)
[@@deriving sexp_of]

and closed_flag = 
  | Closed
      (** [(< | =) row ] *)
  | Open 
      (** [> row ] *)
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
      (** [(P1, ..., Pn)]. Invariant n >= 2. *)
  | Ppat_construct of string * (string list * pattern) option 
      (** [C <P>]. *)
  | Ppat_variant of string * pattern option
      (** [`A <P>]. *)
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
      (** [{l1 = E1; ...; ln = En}] *)
  | Pexp_field of expression * string 
      (** [E.l] *)
  | Pexp_tuple of expression list
      (** Tuples [(E1, ..., En)]. Invariant: n >= 2. *)
  | Pexp_match of expression * case list
      (** Match (or "case") expressions [match E with (P1 -> E1 | ... | Pn -> En)]. *)
  | Pexp_ifthenelse of expression * expression * expression
      (** If (or ternary) expressions [if E then E1 else E2]. *)
  | Pexp_try of expression * case list
      (** [try E0 with P1 -> E1 | ... | Pn -> En] *)
  | Pexp_sequence of expression * expression
      (** [E1; E2] *)
  | Pexp_while of expression * expression
      (** [while E1 do E2 done] *)
  | Pexp_for of pattern * expression * expression * direction_flag * expression
      (** [for i = E1 to E2 do E3 done]
          [for i = E2 downto E2 do E3 done] *)
  | Pexp_variant of string * expression option
      (** [`A <E>] *)
[@@deriving sexp_of]

(** Value bindings [P = E] *)
and value_binding =
  { pvb_forall_vars : string list 
  ; pvb_pat : pattern
  ; pvb_expr : expression
  }
[@@deriving sexp_of]

(** Cases [P -> E]. *)
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

(** External value descriptions {| external x : T = "prim" |} *)
type value_description = 
  { pval_name : string
  ; pval_type : core_scheme
  ; pval_prim : string
  }
[@@deriving sexp_of]

(** [pp_value_description_mach ppf value_desc] pretty prints value description [value_desc] as an explicit tree structure. *)
val pp_value_description_mach : value_description Pretty_printer.t


type type_declaration = 
  { ptype_name : string
      (* Type name [t] *)
  ; ptype_params : string list
      (** Parameters: [('a1, .., 'an) t] *)
  ; ptype_kind : type_decl_kind
      (** Declaration kinds: record or variant *)
  }
[@@deriving sexp_of]

and type_decl_kind = 
  | Ptype_variant of constructor_declaration list
  | Ptype_record of label_declaration list
  | Ptype_abstract
  | Ptype_alias of core_type
[@@deriving sexp_of]

(** Label declaration: [l : 'b1 .. 'bm. T] *)
and label_declaration =
  { plabel_name : string
      (** Label name [l] *)
  ; plabel_betas : string list
      (** Label betas, used for semi-explicit first-class polymorphism *)
  ; plabel_arg : core_type
      (** Label argument type *)
  }
[@@deriving sexp_of]

(** Constructor declaration: [C of 'b1 .. 'bm. T constraint E] *)
and constructor_declaration =
  { pconstructor_name : string
      (** Constructor name [C] *)
  ; pconstructor_arg : constructor_argument option
      (** Constructor argument *)
  ; pconstructor_constraints : (core_type * core_type) list
      (** Constructor constraints (used for GADTs) *)
  }
[@@deriving sexp_of]

and constructor_argument =
  { pconstructor_arg_betas : string list
  ; pconstructor_arg_type : core_type
  }
[@@deriving sexp_of]

(** [pp_type_declaration_mach ppf type_decl] pretty prints [type_decl] using explicit tree structure. *)
val pp_type_declaration_mach : type_declaration Pretty_printer.t 

(** [pp_type_declaration ppf type_decl] pretty prints a [type_decl] as a syntax representation. *)
val pp_type_declaration : type_declaration Pretty_printer.t

(** [pp_label_declaration_mach ppf label_decl] pretty prints [label_decl] using explicit tree structure. *)
val pp_label_declaration_mach : label_declaration Pretty_printer.t 

(** [pp_label_declaration ppf label_decl] pretty prints a [label_decl] as a syntax representation. *)
val pp_label_declaration : label_declaration Pretty_printer.t

(** [pp_constructor_declaration_mach ppf constr_decl] pretty prints [constr_decl] using explicit tree structure. *)
val pp_constructor_declaration_mach : constructor_declaration Pretty_printer.t 

(** [pp_constructor_declaration ppf constr_decl] pretty prints a [constr_decl] as a syntax representation. *)
val pp_constructor_declaration : constructor_declaration Pretty_printer.t


(** Extension constructor [type ('a1, ... 'an) t += ...] *)
type extension_constructor = 
  { pext_name : string
      (** Extension type name [t]. *)
  ; pext_params : string list
      (** Extension type params: [('a1, ..., 'an)]. *)
  ; pext_kind : extension_constructor_kind 
  }
[@@derving sexp_of]

and extension_constructor_kind = 
  | Pext_decl of constructor_declaration
      (** [C of 'b1 .. 'bm. T constraint E] *)
[@@derving sexp_of]

(** [pp_extension_constructor_mach ppf ext_constr] pretty prints [ext_constr] using explicit tree structure. *)
val pp_extension_constructor_mach : extension_constructor Pretty_printer.t 

(** [pp_extension_constructor ppf ext_constr] pretty prints a [ext_constr] as a syntax representation. *)
val pp_extension_constructor : extension_constructor Pretty_printer.t


(** Exception [exception C <of T>] *)
type type_exception = 
  { ptyexn_constructor : extension_constructor }
[@@derving sexp_of]

type structure_item = 
  | Pstr_value of rec_flag * value_binding list
      (** Structure let binding: [let <rec> P1 = E1 and ... and Pn = En] *)
  | Pstr_primitive of value_description
      (** External primitive descriptions *)
  | Pstr_type of type_declaration list
      (** Type declarations [type t1 = ... and ... tn = ...] *)
  | Pstr_exception of type_exception
      (** Exception [exception C <of T>] *)
[@@deriving sexp_of]

val pp_structure_item_mach : structure_item Pretty_printer.t

val pp_structure_item : structure_item Pretty_printer.t

(** Structures -- a list of structure items *)
type structure = structure_item list [@@deriving sexp_of]

val pp_structure_mach : structure Pretty_printer.t

val pp_structure : structure Pretty_printer.t
