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
and 'a abstraction = Type_var.t list * 'a [@@deriving sexp_of]

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
  | Tpat_variant of variant_description * pattern option
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
  | Texp_variant of variant_description * expression option
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

type value_description =
  { tval_name : string
  ; tval_type : scheme
  ; tval_prim : string
  }
[@@deriving sexp_of]

type extension_constructor =
  { text_name : string
  ; text_params : type_var list
  ; text_kind : extension_constructor_kind
  }
[@@derving sexp_of]

and extension_constructor_kind = Text_decl of constructor_declaration
[@@derving sexp_of]

and type_exception = { tyexn_constructor : extension_constructor }
[@@derving sexp_of]

and type_extension =
  { tyext_name : string
  ; tyext_constructors : extension_constructor list
  }
[@@deriving sexp_of]

and structure_item =
  | Tstr_value of value_binding list
  | Tstr_value_rec of rec_value_binding list
  | Tstr_primitive of value_description
  | Tstr_type of type_declaration list
  | Tstr_typext of type_extension
  | Tstr_exception of type_exception
[@@deriving sexp_of]

type structure = structure_item list [@@deriving sexp_of]

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
  | Tpat_variant (variant_desc, pat) ->
    print "Variant";
    pp_variant_description_mach ~indent ppf variant_desc;
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
  | Texp_variant (variant_desc, exp) ->
    print "Variant";
    pp_variant_description_mach ~indent ppf variant_desc;
    (match exp with
    | None -> ()
    | Some exp -> pp_expression_mach ~indent ppf exp)


and pp_value_bindings_mach ~indent ppf value_bindings =
  Format.fprintf ppf "%sValue bindings:@." indent;
  let indent = indent_space ^ indent in
  List.iter ~f:(pp_value_binding_mach ~indent ppf) value_bindings


and pp_label_exp_mach ~indent ppf (label_desc, exp) =
  pp_label_description_mach ~indent ppf label_desc;
  pp_expression_mach ~indent ppf exp


and pp_abstraction_mach ~indent ~pp ppf ((variables, t) : _ abstraction) =
  Format.fprintf ppf "%sAbstraction:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf
    ppf
    "%sVariables: %s@."
    indent
    (List.map variables ~f:(fun var -> var |> Type_var.id |> Int.to_string)
    |> String.concat ~sep:",");
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


let pp_scheme_mach ~indent ppf (variables, type_expr) =
  Format.fprintf ppf "%sScheme:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf
    ppf
    "%sVariables: %s@."
    indent
    (String.concat
       ~sep:","
       (List.map ~f:(fun t -> Type_var.id t |> Int.to_string) variables));
  pp_type_expr_mach ~indent ppf type_expr


let pp_value_description_mach ~indent ppf value_desc =
  Format.fprintf ppf "%sValue description:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sName: %s@." indent value_desc.tval_name;
  pp_scheme_mach ~indent ppf value_desc.tval_type;
  Format.fprintf ppf "%sPrimitive name: %s@." indent value_desc.tval_prim


let pp_extension_constructor_kind_mach ~indent ppf ext_constr_kind =
  let print = Format.fprintf ppf "%sExtension constructor kind: %s@." indent in
  let indent = indent_space ^ indent in
  match ext_constr_kind with
  | Text_decl constr_decl ->
    print "Declaration";
    pp_constructor_declaration_mach ~indent ppf constr_decl


let pp_extension_constructor_mach ~indent ppf ext_constr =
  Format.fprintf ppf "%sExtension constructor:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sExtension name: %s@." indent ext_constr.text_name;
  Format.fprintf
    ppf
    "%sExtension parameters: %s@."
    indent
    (String.concat
       ~sep:" "
       (List.map
          ~f:(fun t -> Type_var.id t |> Int.to_string)
          ext_constr.text_params));
  pp_extension_constructor_kind_mach ~indent ppf ext_constr.text_kind


let pp_type_exception_mach ~indent ppf type_exn =
  Format.fprintf ppf "%sType exception:@." indent;
  let indent = indent_space ^ indent in
  pp_extension_constructor_mach ~indent ppf type_exn.tyexn_constructor


let pp_type_extension_mach ~indent ppf type_ext =
  Format.fprintf ppf "%sType extension:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sExtension name: %s@." indent type_ext.tyext_name;
  List.iter
    ~f:(pp_extension_constructor_mach ~indent ppf)
    type_ext.tyext_constructors


let pp_structure_item_mach ~indent ppf str_item =
  let print = Format.fprintf ppf "%sStructure item: %s@." indent in
  let indent = indent_space ^ indent in
  match str_item with
  | Tstr_value value_bindings ->
    print "Let";
    pp_value_bindings_mach ~indent ppf value_bindings
  | Tstr_value_rec rec_value_bindings ->
    print "Let";
    pp_rec_value_bindings_mach ~indent ppf rec_value_bindings
  | Tstr_primitive value_desc ->
    print "Primitive";
    pp_value_description_mach ~indent ppf value_desc
  | Tstr_type type_decls ->
    print "Type";
    List.iter type_decls ~f:(pp_type_declaration_mach ~indent ppf)
  | Tstr_exception type_exception ->
    print "Exception";
    pp_type_exception_mach ~indent ppf type_exception
  | Tstr_typext type_ext ->
    print "Type Extension";
    pp_type_extension_mach ~indent ppf type_ext


let pp_structure_mach ~indent ppf str =
  Format.fprintf ppf "%sStructure:@." indent;
  let indent = indent_space ^ indent in
  List.iter str ~f:(pp_structure_item_mach ~indent ppf)


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

(* let pp_structure_item_mach =
  to_pp_mach ~name:"Structure item" ~pp:pp_structure_item_mach *)

let pp_structure_mach = to_pp_mach ~name:"Structure" ~pp:pp_structure_mach
let pp_expression _ppf = assert false
let pp_value_binding _ppf = assert false
let pp_rec_value_binding _ppf = assert false
let pp_case _ppf = assert false
