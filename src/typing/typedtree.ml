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

(** Abstract syntax tree after typing *)

type 'a instance = 'a * type_expr list [@@deriving sexp_of]
and 'a abstraction = string list * 'a [@@deriving sexp_of]

type pattern =
  { pat_desc : pattern_desc
  ; pat_type : type_expr
  }
[@@deriving sexp_of]

and pattern_desc =
  | Tpat_any
  | Tpat_var of string
  | Tpat_alias of pattern * string
  | Tpat_const of constant
  | Tpat_tuple of pattern list
  | Tpat_construct of constructor_description * pattern option
[@@deriving sexp_of]

type expression =
  { exp_desc : expression_desc
  ; exp_type : type_expr
  }
[@@deriving sexp_of]

and expression_desc =
  | Texp_var of string instance
  | Texp_prim of primitive
  | Texp_const of constant
  | Texp_fun of pattern * expression
  | Texp_app of expression * expression
  | Texp_let of value_binding list * expression
  | Texp_let_rec of rec_value_binding list * expression
  | Texp_construct of constructor_description * expression option
  | Texp_record of (label_description * expression) list
  | Texp_field of expression * label_description
  | Texp_tuple of expression list
  | Texp_match of expression * type_expr * case list
  | Texp_ifthenelse of expression * expression * expression
  | Texp_try of expression * case list
  | Texp_sequence of expression * expression
  | Texp_while of expression * expression
  | Texp_for of string * expression * expression * direction_flag * expression
[@@deriving sexp_of]

and value_binding =
  { tvb_pat : pattern
  ; tvb_expr : expression abstraction
  }
[@@deriving sexp_of]

and rec_value_binding =
  { trvb_var : string
  ; trvb_expr : expression abstraction
  }
[@@deriving sexp_of]

and case =
  { tc_lhs : pattern
  ; tc_rhs : expression
  }
[@@deriving sexp_of]

let indent_space = "   "

let rec pp_pattern_mach ~indent ppf pat =
  Format.fprintf ppf "%sPattern:@." indent;
  let indent = indent_space ^ indent in
  pp_type_expr_mach ~indent ppf pat.pat_type;
  pp_pattern_desc_mach ~indent ppf pat.pat_desc


and pp_pattern_desc_mach ~indent ppf pat_desc =
  let print = Format.fprintf ppf "%sDesc: %s@." indent in
  let indent = indent_space ^ indent in
  match pat_desc with
  | Tpat_any -> print "Any"
  | Tpat_var x -> print ("Variable: " ^ x)
  | Tpat_alias (pat, x) ->
    print "Alias";
    pp_pattern_mach ~indent ppf pat;
    Format.fprintf ppf "%sAs: %s@." indent x
  | Tpat_const const -> print ("Constant: " ^ string_of_constant const)
  | Tpat_tuple pats ->
    print "Tuple";
    List.iter ~f:(pp_pattern_mach ~indent ppf) pats
  | Tpat_construct (constr_desc, pat) ->
    print "Construct";
    pp_constructor_description_mach ~indent ppf constr_desc;
    (match pat with
    | None -> ()
    | Some pat -> pp_pattern_mach ~indent ppf pat)


let pp_pattern _ppf = assert false

let rec pp_expression_mach ~indent ppf exp =
  Format.fprintf ppf "%sExpression:@." indent;
  let indent = indent_space ^ indent in
  pp_type_expr_mach ~indent ppf exp.exp_type;
  pp_expression_desc_mach ~indent ppf exp.exp_desc


and pp_expression_desc_mach ~indent ppf exp_desc =
  let print = Format.fprintf ppf "%sDesc: %s@." indent in
  let indent = indent_space ^ indent in
  match exp_desc with
  | Texp_var (x, instances) ->
    print "Variable";
    Format.fprintf ppf "%sVariable: %s@." indent x;
    List.iter ~f:(pp_type_expr_mach ~indent ppf) instances
  | Texp_prim prim -> print ("Primitive: " ^ string_of_primitive prim)
  | Texp_const const -> print ("Constant: " ^ string_of_constant const)
  | Texp_fun (pat, exp) ->
    print "Function";
    pp_pattern_mach ~indent ppf pat;
    pp_expression_mach ~indent ppf exp
  | Texp_app (exp1, exp2) ->
    print "Application";
    pp_expression_mach ~indent ppf exp1;
    pp_expression_mach ~indent ppf exp2
  | Texp_let (value_bindings, exp) ->
    print "Let";
    pp_value_bindings_mach ~indent ppf value_bindings;
    pp_expression_mach ~indent ppf exp
  | Texp_let_rec (rec_value_bindings, exp) ->
    print "Let rec";
    pp_rec_value_bindings_mach ~indent ppf rec_value_bindings;
    pp_expression_mach ~indent ppf exp
  | Texp_construct (constr_desc, exp) ->
    print "Construct";
    pp_constructor_description_mach ~indent ppf constr_desc;
    (match exp with
    | None -> ()
    | Some exp -> pp_expression_mach ~indent ppf exp)
  | Texp_record label_exps ->
    print "Record";
    List.iter ~f:(pp_label_exp_mach ~indent ppf) label_exps
  | Texp_field (exp, label_desc) ->
    print "Field";
    pp_expression_mach ~indent ppf exp;
    pp_label_description_mach ~indent ppf label_desc
  | Texp_tuple exps ->
    print "Tuple";
    List.iter ~f:(pp_expression_mach ~indent ppf) exps
  | Texp_match (exp, type_expr, cases) ->
    print "Match";
    pp_expression_mach ~indent ppf exp;
    pp_type_expr_mach ~indent ppf type_expr;
    Format.fprintf ppf "%sCases:@." indent;
    List.iter ~f:(pp_case_mach ~indent:(indent_space ^ indent) ppf) cases
  | Texp_ifthenelse (exp1, exp2, exp3) ->
    print "If";
    pp_expression_mach ~indent ppf exp1;
    pp_expression_mach ~indent ppf exp2;
    pp_expression_mach ~indent ppf exp3
  | Texp_try (exp, cases) ->
    print "Try";
    pp_expression_mach ~indent ppf exp;
    Format.fprintf ppf "%sCases:@." indent;
    List.iter ~f:(pp_case_mach ~indent:(indent_space ^ indent) ppf) cases
  | Texp_sequence (exp1, exp2) ->
    print "Sequence";
    pp_expression_mach ~indent ppf exp1;
    pp_expression_mach ~indent ppf exp2
  | Texp_while (exp1, exp2) ->
    print "While";
    pp_expression_mach ~indent ppf exp1;
    pp_expression_mach ~indent ppf exp2
  | Texp_for (index, exp1, exp2, direction_flag, exp3) ->
    print "For";
    Format.fprintf ppf "%sIndex: %s@." indent index;
    pp_expression_mach ~indent ppf exp1;
    Format.fprintf
      ppf
      "%sDirection: %s@."
      indent
      (string_of_direction_flag direction_flag);
    pp_expression_mach ~indent ppf exp2;
    pp_expression_mach ~indent ppf exp3


and pp_value_bindings_mach ~indent ppf value_bindings =
  Format.fprintf ppf "%sValue bindings:@." indent;
  let indent = indent_space ^ indent in
  List.iter ~f:(pp_value_binding_mach ~indent ppf) value_bindings


and pp_label_exp_mach ~indent ppf (label_desc, exp) =
  pp_label_description_mach ~indent ppf label_desc;
  pp_expression_mach ~indent ppf exp


and pp_abstraction_mach ~indent ~pp ppf (variables, t) =
  Format.fprintf ppf "%sAbstraction:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf
    ppf
    "%sVariables: %s@."
    indent
    (String.concat ~sep:"," variables);
  pp ~indent ppf t


and pp_value_binding_mach ~indent ppf value_binding =
  Format.fprintf ppf "%sValue binding:@." indent;
  let indent = indent_space ^ indent in
  pp_pattern_mach ~indent ppf value_binding.tvb_pat;
  pp_abstraction_mach ~indent ~pp:pp_expression_mach ppf value_binding.tvb_expr


and pp_rec_value_bindings_mach ~indent ppf rec_value_bindings =
  Format.fprintf ppf "%sValue bindings:@." indent;
  let indent = indent_space ^ indent in
  List.iter ~f:(pp_rec_value_binding_mach ~indent ppf) rec_value_bindings


and pp_rec_value_binding_mach ~indent ppf value_binding =
  Format.fprintf ppf "%sValue binding:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sVariable: %s@." indent value_binding.trvb_var;
  pp_abstraction_mach ~indent ~pp:pp_expression_mach ppf value_binding.trvb_expr


and pp_case_mach ~indent ppf case =
  Format.fprintf ppf "%sCase:@." indent;
  let indent = indent_space ^ indent in
  pp_pattern_mach ~indent ppf case.tc_lhs;
  pp_expression_mach ~indent ppf case.tc_rhs


let to_pp_mach ~pp ~name ppf t =
  Format.fprintf ppf "%s:@." name;
  let indent = "└──" in
  pp ~indent ppf t


let pp_pattern_mach = to_pp_mach ~pp:pp_pattern_mach ~name:"Pattern"
let pp_expression_mach = to_pp_mach ~pp:pp_expression_mach ~name:"Expression"

let pp_value_binding_mach =
  to_pp_mach ~pp:pp_value_binding_mach ~name:"Value binding"


let pp_rec_value_binding_mach =
  to_pp_mach ~pp:pp_rec_value_binding_mach ~name:"Value binding"


let pp_case_mach = to_pp_mach ~pp:pp_case_mach ~name:"Case"
let pp_expression _ppf = assert false
let pp_value_binding _ppf = assert false
let pp_rec_value_binding _ppf = assert false
let pp_case _ppf = assert false
