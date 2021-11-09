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

(* ------------------------------------------------------------------------- *)

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
  (** A type constructor (or "type former"),
      name "constr" is used for consistency between OCaml and Dromedary code. *)
  

(** [core_schemes] are defined by the grammar: 
    core_schemes ::= 'a1 ... 'an. T 
    
    This "source"-level notion of type schemes is often used
    in annotations in [expression] and [pattern]. *)
type core_scheme = string list * core_type

type pattern = 
  | Ppat_any 
  (** [_]. *)
  | Ppat_var of string
  (** [x]. *)
  | Ppat_alias of pattern * string
  (** [P as x]. *)
  | Ppat_constant of constant
  (** [c]. e.g. [1, true, ()]. *)
  | Ppat_tuple of pattern list
  (** (P1, ..., Pn). Invariant n >= 2. *)
  | Ppat_construct of string * pattern option
  (** [C <P>]. *)
  | Ppat_record of (string * pattern) list 
  (** { l1=P1; ...; ln = Pn } *)
  | Ppat_constraint of pattern * core_type
  (** [(P : T)]. *)

type expression = 
  | Pexp_var of string
  (** [x]. *)
  | Pexp_prim of primitive
  (** Primitive operations [%prim p]. e.g. [%prim +], [%prim -], etc. *)
  | Pexp_const of constant
  (** Constants [c]. e.g. [1, true, ()]. *)
  | Pexp_fun of pattern list * expression
  (** The function (or lambda) abstraction [fun P -> E].  
      Note that: 
        - [let x P1 ... Pn = E in ...] is encoding using 
          [Pexp_let ("x", fun P1 ... Pn -> E, ...)]. *)
  | Pexp_app of expression * expression
  (** Function application [E1 E2]. *)
  | Pexp_let of rec_flag * value_binding * expression
  (** Let expressions:
      [let P1 = E1 and ... and Pn = En in E]      ([rec_flag = Nonrecursive]).    
      [let rec P1 = E1 and ... Pn = En in E]      ([rec_flag = Recursive]). 
      
      TODO: Improve this definition. Split rec and nonrec (perhaps using GADTs?) w/ dependent value_binding types *)
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
  (** Tuples [(E1, ..., En)]. 
      Invariant: n >= 2. *)
  | Pexp_match of expression * case list
  (** Match (or "case") expressions [match E with (P1 -> E1 | ... | Pn -> En)]. *)
  | Pexp_ifthenelse of expression * expression * expression
  (** If (or ternary) expressions [if E then E1 else E2]. *)


(** [P = E]. *)
and value_binding = 
  { pvb_pat : pattern
  ; pvb_expr : expression
  } 

(** [P -> E]. *)
and case = 
  { pc_lhs : pattern
  ; pc_rhs : expression
  }