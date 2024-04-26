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
open Ast_types

(** [Parsetree] is the abstract syntax tree produced by parsing
    Dromedary's source code. *)

type core_type =
  | Ptyp_var of string
  | Ptyp_arrow of core_type * core_type
  | Ptyp_tuple of core_type list
  | Ptyp_constr of core_type list * string
  | Ptyp_variant of row
  | Ptyp_mu of string * core_type
  | Ptyp_where of core_type * string * core_type
[@@deriving sexp_of]

and row = row_field list * closed_flag
and row_field = Row_tag of string * core_type option

and closed_flag =
  | Closed
  | Open

type core_scheme = string list * core_type [@@deriving sexp_of]

type pattern =
  | Ppat_any
  | Ppat_var of string
  | Ppat_alias of pattern * string
  | Ppat_const of constant
  | Ppat_tuple of pattern list
  | Ppat_construct of string * (string list * pattern) option
  | Ppat_variant of string * pattern option
  | Ppat_constraint of pattern * core_type
[@@deriving sexp_of]

type expression =
  | Pexp_var of string
  | Pexp_prim of primitive
  | Pexp_const of constant
  | Pexp_fun of pattern * expression
  | Pexp_app of expression * expression
  | Pexp_let of rec_flag * value_binding list * expression
  | Pexp_forall of string list * expression
  | Pexp_exists of string list * expression
  | Pexp_constraint of expression * core_type
  | Pexp_construct of string * expression option
  | Pexp_record of (string * expression) list
  | Pexp_field of expression * string
  | Pexp_tuple of expression list
  | Pexp_match of expression * case list
  | Pexp_ifthenelse of expression * expression * expression
  | Pexp_try of expression * case list
  | Pexp_sequence of expression * expression
  | Pexp_while of expression * expression
  | Pexp_for of pattern * expression * expression * direction_flag * expression
  | Pexp_variant of string * expression option
[@@deriving sexp_of]

and value_binding =
  { pvb_forall_vars : string list
  ; pvb_pat : pattern
  ; pvb_expr : expression
  }

and case =
  { pc_lhs : pattern
  ; pc_rhs : expression
  }

type value_description =
  { pval_name : string
  ; pval_type : core_scheme
  ; pval_prim : string
  }
[@@deriving sexp_of]

type type_declaration =
  { ptype_name : string
  ; ptype_params : string list
  ; ptype_kind : type_decl_kind
  }
[@@deriving sexp_of]

and type_decl_kind =
  | Ptype_variant of constructor_declaration list
  | Ptype_record of label_declaration list
  | Ptype_abstract
  | Ptype_alias of core_type
  | Ptype_open

and label_declaration =
  { plabel_name : string
  ; plabel_betas : string list
  ; plabel_arg : core_type
  }

and constructor_declaration =
  { pconstructor_name : string
  ; pconstructor_arg : constructor_argument option
  ; pconstructor_constraints : (core_type * core_type) list
  }

and constructor_argument =
  { pconstructor_arg_betas : string list
  ; pconstructor_arg_type : core_type
  }

type extension_constructor = { pext_kind : extension_constructor_kind }
[@@deriving sexp_of]

and extension_constructor_kind = Pext_decl of constructor_declaration

type type_extension =
  { ptyext_name : string
  ; ptyext_params : string list
  ; ptyext_constructors : extension_constructor list
  }
[@@deriving sexp_of]

type structure_item =
  | Pstr_value of rec_flag * value_binding list
  | Pstr_primitive of value_description
  | Pstr_type of type_declaration list
  | Pstr_typext of type_extension
  | Pstr_exception of type_exception
[@@deriving sexp_of]

and type_exception = { ptyexn_constructor : extension_constructor }

type structure = structure_item list [@@deriving sexp_of]

(* "Machine format" pretty prints display terms using an explicit tree structure,
   using indentations to mark new structures.

   For example:
   {[
     val curry : Parsetree.expression

     pp_expression_mach Format.std_formatter curry;;
     Expression:
     └──Expression: Function
        └──Pattern: Variable: f
        └──Expression: Function
           └──Pattern: Variable: x
           └──Expression: Function
              └──Pattern: Variable: y
              └──Expression: Application
                 └──Expression: Variable: f
                 └──Expression: Tuple
                    └──Expression: Variable: x
                    └──Expression: Variable: y
   ]}

   This is rather useful for expect tests, etc, where an explicit tree-like
   structure is clearer (for correctness).
*)

let indent_space = "   "

let string_of_closed_flag closed_flag =
  match closed_flag with
  | Open -> "Open"
  | Closed -> "Closed"


let rec pp_core_type_mach ~indent ppf core_type =
  let pr = Fmt.pf ppf "%sType: %s@." indent in
  let indent = indent_space ^ indent in
  match core_type with
  | Ptyp_var x ->
    pr "Variable";
    Fmt.pf ppf "%sVariable: %s@." indent x
  | Ptyp_arrow (t1, t2) ->
    pr "Arrow";
    pp_core_type_mach ~indent ppf t1;
    pp_core_type_mach ~indent ppf t2
  | Ptyp_tuple ts ->
    pr "Tuple";
    List.iter ~f:(pp_core_type_mach ~indent ppf) ts
  | Ptyp_constr (ts, constr) ->
    pr "Constructor";
    Fmt.pf ppf "%sConstructor: %s@." indent constr;
    List.iter ~f:(pp_core_type_mach ~indent ppf) ts
  | Ptyp_variant row ->
    pr "Variant";
    pp_row_mach ~indent ppf row
  | Ptyp_mu (x, t) ->
    pr "Mu";
    Fmt.pf ppf "%sVariable: %s@." indent x;
    pp_core_type_mach ~indent ppf t
  | Ptyp_where (t1, x, t2) ->
    pr "Where";
    Fmt.pf ppf "%sVariable: %s@." indent x;
    pp_core_type_mach ~indent ppf t2;
    pp_core_type_mach ~indent ppf t1


and pp_row_mach ~indent ppf (row_fields, closed_flag) =
  Fmt.pf ppf "%sRow: %s@." indent (string_of_closed_flag closed_flag);
  let indent = indent_space ^ indent in
  List.iter ~f:(pp_row_field_mach ~indent ppf) row_fields


and pp_row_field_mach ~indent ppf row_field =
  let pr = Fmt.pf ppf "%sRow field: %s@." indent in
  let indent = indent_space ^ indent in
  match row_field with
  | Row_tag (tag, core_type) ->
    pr "Tag";
    Fmt.pf ppf "%sField tag: %s@." indent tag;
    Option.iter core_type ~f:(pp_core_type_mach ~indent ppf)


let pp_core_scheme_mach ~indent ppf (variables, core_type) =
  Fmt.pf ppf "%sScheme:@." indent;
  let indent = indent_space ^ indent in
  let variables =
    match variables with
    | [] -> "[]"
    | variables -> String.concat ~sep:"," variables
  in
  Fmt.pf ppf "%sVariables: %s@." indent variables;
  pp_core_type_mach ~indent ppf core_type


let rec pp_pattern_mach ~indent ppf pat =
  let pr = Fmt.pf ppf "%sPattern: %s@." indent in
  let indent = indent_space ^ indent in
  match pat with
  | Ppat_any -> pr "Any"
  | Ppat_var x -> pr ("Variable: " ^ x)
  | Ppat_alias (pat, x) ->
    pr "Alias";
    pp_pattern_mach ~indent ppf pat;
    Fmt.pf ppf "%sAs: %s@." indent x
  | Ppat_const const -> pr ("Constant: " ^ string_of_constant const)
  | Ppat_tuple pats ->
    pr "Tuple";
    List.iter ~f:(pp_pattern_mach ~indent ppf) pats
  | Ppat_construct (constr, pat) ->
    pr "Construct";
    Fmt.pf ppf "%sConstructor: %s@." indent constr;
    (match pat with
     | None -> ()
     | Some (_, pat) -> pp_pattern_mach ~indent ppf pat)
  | Ppat_variant (tag, pat) ->
    pr "Variant";
    Fmt.pf ppf "%sTag: %s@." indent tag;
    (match pat with
     | None -> ()
     | Some pat -> pp_pattern_mach ~indent ppf pat)
  | Ppat_constraint (pat, core_type) ->
    pr "Constraint";
    pp_pattern_mach ~indent ppf pat;
    pp_core_type_mach ~indent ppf core_type


let rec pp_expression_mach ~indent ppf exp =
  let pr = Fmt.pf ppf "%sExpression: %s@." indent in
  let indent = indent_space ^ indent in
  match exp with
  | Pexp_var x -> pr ("Variable: " ^ x)
  | Pexp_prim prim -> pr ("Primitive: " ^ string_of_primitive prim)
  | Pexp_const const -> pr ("Constant: " ^ string_of_constant const)
  | Pexp_fun (pat, exp) ->
    pr "Function";
    pp_pattern_mach ~indent ppf pat;
    pp_expression_mach ~indent ppf exp
  | Pexp_app (exp1, exp2) ->
    pr "Application";
    pp_expression_mach ~indent ppf exp1;
    pp_expression_mach ~indent ppf exp2
  | Pexp_let (rec_flag, value_bindings, exp) ->
    pr ("Let: " ^ string_of_rec_flag rec_flag);
    pp_value_bindings_mach ~indent ppf value_bindings;
    pp_expression_mach ~indent ppf exp
  | Pexp_forall (variables, exp) ->
    pr "Forall";
    let variables = String.concat ~sep:"," variables in
    Fmt.pf ppf "%sVariables: %s@." indent variables;
    pp_expression_mach ~indent ppf exp
  | Pexp_exists (variables, exp) ->
    pr "Exists";
    let variables = String.concat ~sep:"," variables in
    Fmt.pf ppf "%sVariables: %s@." indent variables;
    pp_expression_mach ~indent ppf exp
  | Pexp_constraint (exp, core_type) ->
    pr "Constraint";
    pp_expression_mach ~indent ppf exp;
    pp_core_type_mach ~indent ppf core_type
  | Pexp_construct (constr, exp) ->
    pr "Construct";
    Fmt.pf ppf "%sConstructor: %s@." indent constr;
    (match exp with
     | None -> ()
     | Some exp -> pp_expression_mach ~indent ppf exp)
  | Pexp_record label_exps ->
    pr "Record";
    List.iter ~f:(pp_label_exp_mach ~indent ppf) label_exps
  | Pexp_field (exp, label) ->
    pr "Field";
    pp_expression_mach ~indent ppf exp;
    Fmt.pf ppf "%sLabel: %s@." indent label
  | Pexp_tuple exps ->
    pr "Tuple";
    List.iter ~f:(pp_expression_mach ~indent ppf) exps
  | Pexp_match (exp, cases) ->
    pr "Match";
    pp_expression_mach ~indent ppf exp;
    Fmt.pf ppf "%sCases:@." indent;
    List.iter ~f:(pp_case_mach ~indent:(indent_space ^ indent) ppf) cases
  | Pexp_ifthenelse (exp1, exp2, exp3) ->
    pr "If";
    pp_expression_mach ~indent ppf exp1;
    pp_expression_mach ~indent ppf exp2;
    pp_expression_mach ~indent ppf exp3
  | Pexp_try (exp, cases) ->
    pr "Try";
    pp_expression_mach ~indent ppf exp;
    Fmt.pf ppf "%sCases:@." indent;
    List.iter ~f:(pp_case_mach ~indent:(indent_space ^ indent) ppf) cases
  | Pexp_sequence (exp1, exp2) ->
    pr "Sequence";
    pp_expression_mach ~indent ppf exp1;
    pp_expression_mach ~indent ppf exp2
  | Pexp_while (exp1, exp2) ->
    pr "While";
    pp_expression_mach ~indent ppf exp1;
    pp_expression_mach ~indent ppf exp2
  | Pexp_for (pat, exp1, exp2, direction_flag, exp3) ->
    pr "For";
    pp_pattern_mach ~indent ppf pat;
    pp_expression_mach ~indent ppf exp1;
    Fmt.pf
      ppf
      "%sDirection: %s@."
      indent
      (string_of_direction_flag direction_flag);
    pp_expression_mach ~indent ppf exp2;
    pp_expression_mach ~indent ppf exp3
  | Pexp_variant (tag, exp) ->
    pr "Variant";
    Fmt.pf ppf "%sTag: %s@." indent tag;
    (match exp with
     | None -> ()
     | Some exp -> pp_expression_mach ~indent ppf exp)


and pp_value_bindings_mach ~indent ppf value_bindings =
  Fmt.pf ppf "%sValue bindings:@." indent;
  let indent = indent_space ^ indent in
  List.iter ~f:(pp_value_binding_mach ~indent ppf) value_bindings


and pp_label_exp_mach ~indent ppf (label, exp) =
  Fmt.pf ppf "%sLabel: %s@." indent label;
  let indent = indent_space ^ indent in
  pp_expression_mach ~indent ppf exp


and pp_value_binding_mach ~indent ppf value_binding =
  Fmt.pf ppf "%sValue binding:@." indent;
  let indent = indent_space ^ indent in
  pp_pattern_mach ~indent ppf value_binding.pvb_pat;
  pp_expression_mach ~indent ppf value_binding.pvb_expr


and pp_case_mach ~indent ppf case =
  Fmt.pf ppf "%sCase:@." indent;
  let indent = indent_space ^ indent in
  pp_pattern_mach ~indent ppf case.pc_lhs;
  pp_expression_mach ~indent ppf case.pc_rhs


let pp_value_description_mach ~indent ppf value_desc =
  Fmt.pf ppf "%sValue description:@." indent;
  let indent = indent_space ^ indent in
  Fmt.pf ppf "%sName: %s@." indent value_desc.pval_name;
  pp_core_scheme_mach ~indent ppf value_desc.pval_type;
  Fmt.pf ppf "%sPrimitive name: %s@." indent value_desc.pval_prim


let pp_constraint_mach ~indent ppf (lhs, rhs) =
  Fmt.pf ppf "%sConstraint:@." indent;
  let indent = indent_space ^ indent in
  pp_core_type_mach ~indent ppf lhs;
  pp_core_type_mach ~indent ppf rhs


let pp_constructor_argument_mach ~indent ppf constr_arg =
  Fmt.pf ppf "%sConstructor argument:@." indent;
  let indent = indent_space ^ indent in
  Fmt.pf
    ppf
    "%sConstructor existentials: %s@."
    indent
    (String.concat ~sep:" " constr_arg.pconstructor_arg_betas);
  pp_core_type_mach ~indent ppf constr_arg.pconstructor_arg_type


let pp_constructor_declaration_mach ~indent ppf constr_decl =
  Fmt.pf ppf "%sConstructor declaration:@." indent;
  let indent = indent_space ^ indent in
  Fmt.pf ppf "%sConstructor name: %s@." indent constr_decl.pconstructor_name;
  (match constr_decl.pconstructor_arg with
   | None -> ()
   | Some constr_arg -> pp_constructor_argument_mach ~indent ppf constr_arg);
  List.iter
    ~f:(pp_constraint_mach ~indent ppf)
    constr_decl.pconstructor_constraints


let pp_label_declaration_mach ~indent ppf label_decl =
  Fmt.pf ppf "%sLabel declaration:@." indent;
  let indent = indent_space ^ indent in
  Fmt.pf ppf "%sLabel name: %s@." indent label_decl.plabel_name;
  Fmt.pf
    ppf
    "%sLabel polymorphic parameters: %s@."
    indent
    (String.concat ~sep:" " label_decl.plabel_betas);
  pp_core_type_mach ~indent ppf label_decl.plabel_arg


let pp_type_decl_kind_mach ~indent ppf type_decl_kind =
  let pr = Fmt.pf ppf "%sType declaration kind: %s@." indent in
  let indent = indent_space ^ indent in
  match type_decl_kind with
  | Ptype_variant constr_decls ->
    pr "Variant";
    List.iter constr_decls ~f:(pp_constructor_declaration_mach ~indent ppf)
  | Ptype_record label_decls ->
    pr "Record";
    List.iter label_decls ~f:(pp_label_declaration_mach ~indent ppf)
  | Ptype_abstract -> pr "Abstract"
  | Ptype_alias core_type ->
    pr "Alias";
    pp_core_type_mach ~indent ppf core_type
  | Ptype_open -> pr "Open"


let pp_type_declaration_mach ~indent ppf type_decl =
  Fmt.pf ppf "%sType declaration:@." indent;
  let indent = indent_space ^ indent in
  Fmt.pf ppf "%sType name: %s@." indent type_decl.ptype_name;
  Fmt.pf
    ppf
    "%sType parameters: %s@."
    indent
    (String.concat ~sep:" " type_decl.ptype_params);
  pp_type_decl_kind_mach ~indent ppf type_decl.ptype_kind


let pp_extension_constructor_kind_mach ~indent ppf ext_constr_kind =
  let pr = Fmt.pf ppf "%sExtension constructor kind: %s@." indent in
  let indent = indent_space ^ indent in
  match ext_constr_kind with
  | Pext_decl constr_decl ->
    pr "Declaration";
    pp_constructor_declaration_mach ~indent ppf constr_decl


let pp_extension_constructor_mach ~indent ppf ext_constr =
  Fmt.pf ppf "%sExtension constructor:@." indent;
  let indent = indent_space ^ indent in
  (* Fmt.pf ppf "%sExtension name: %s@." indent ext_constr.pext_name;
     Fmt.pf
     ppf
     "%sExtension parameters: %s@."
     indent
     (String.concat ~sep:" " ext_constr.pext_params); *)
  pp_extension_constructor_kind_mach ~indent ppf ext_constr.pext_kind


let pp_type_exception_mach ~indent ppf type_exn =
  Fmt.pf ppf "%sType exception:@." indent;
  let indent = indent_space ^ indent in
  pp_extension_constructor_mach ~indent ppf type_exn.ptyexn_constructor


let pp_type_extension_mach ~indent ppf type_ext =
  Fmt.pf ppf "%sType extension:@." indent;
  let indent = indent_space ^ indent in
  Fmt.pf ppf "%sExtension name: %s@." indent type_ext.ptyext_name;
  Fmt.pf
    ppf
    "%sExtension parameters: %s@."
    indent
    (String.concat ~sep:" " type_ext.ptyext_params);
  List.iter
    type_ext.ptyext_constructors
    ~f:(pp_extension_constructor_mach ~indent ppf)


let pp_structure_item_mach ~indent ppf str_item =
  let pr = Fmt.pf ppf "%sStructure item: %s@." indent in
  let indent = indent_space ^ indent in
  match str_item with
  | Pstr_value (rec_flag, value_bindings) ->
    pr ("Let: " ^ string_of_rec_flag rec_flag);
    pp_value_bindings_mach ~indent ppf value_bindings
  | Pstr_primitive value_desc ->
    pr "Primitive";
    pp_value_description_mach ~indent ppf value_desc
  | Pstr_type type_decls ->
    pr "Type";
    List.iter type_decls ~f:(pp_type_declaration_mach ~indent ppf)
  | Pstr_exception type_exception ->
    pr "Exception";
    pp_type_exception_mach ~indent ppf type_exception
  | Pstr_typext type_extension ->
    pr "Type Extension";
    pp_type_extension_mach ~indent ppf type_extension


let pp_structure_mach ~indent ppf str =
  Fmt.pf ppf "%sStructure:@." indent;
  let indent = indent_space ^ indent in
  List.iter str ~f:(pp_structure_item_mach ~indent ppf)


let to_pp_mach ~name ~pp ppf t =
  Fmt.pf ppf "%s:@." name;
  let indent = "└──" in
  pp ~indent ppf t


let pp_core_type_mach = to_pp_mach ~name:"Core type" ~pp:pp_core_type_mach
let pp_core_scheme_mach = to_pp_mach ~name:"Core scheme" ~pp:pp_core_scheme_mach
let pp_pattern_mach = to_pp_mach ~name:"Pattern" ~pp:pp_pattern_mach
let pp_expression_mach = to_pp_mach ~name:"Expression" ~pp:pp_expression_mach

let pp_value_binding_mach =
  to_pp_mach ~name:"Value binding" ~pp:pp_value_binding_mach


let pp_case_mach = to_pp_mach ~name:"Case" ~pp:pp_case_mach

let pp_value_description_mach =
  to_pp_mach ~name:"Value description" ~pp:pp_value_description_mach


let pp_type_declaration_mach =
  to_pp_mach ~name:"Type declaration" ~pp:pp_type_declaration_mach


let pp_label_declaration_mach =
  to_pp_mach ~name:"Label declaration" ~pp:pp_label_declaration_mach


let pp_constructor_declaration_mach =
  to_pp_mach ~name:"Constructor declaration" ~pp:pp_constructor_declaration_mach


let pp_extension_constructor_mach =
  to_pp_mach ~name:"Extension constructor" ~pp:pp_extension_constructor_mach


let pp_structure_item_mach =
  to_pp_mach ~name:"Structure item" ~pp:pp_structure_item_mach


let pp_structure_mach = to_pp_mach ~name:"Structure" ~pp:pp_structure_mach

(* "Human format" (or standard) pretty printer display the terms using their
   syntactic representation. This is often used in error reporting, etc.

   For example:
   {[
     val map : Parsetree.expression

     pp_expression Format.std_formatter map;;
     let rec map f xs =
       match xs with (Nil -> Nil | Cons (x, xs) -> Cons (f x, map f xs)) in
     map Nil
   ]}
*)

let star = Fmt.any "@;*@;"
let vbar = Fmt.any "@;|@;"

let rec pp_core_type ppf core_type =
  let pp_parens ~parens pp = if parens then Fmt.parens pp else pp in
  let rec loop ?(parens = false) ppf core_type =
    match core_type with
    | Ptyp_var x -> Fmt.pf ppf "%s" x
    | Ptyp_arrow (t1, t2) ->
      pp_parens
        ~parens
        Fmt.(
          fun ppf (t1, t2) ->
            pf
              ppf
              "@[%a@;->@;%a@]"
              (loop ~parens:true)
              t1
              (loop ~parens:false)
              t2)
        ppf
        (t1, t2)
    | Ptyp_tuple ts ->
      pp_parens ~parens Fmt.(list ~sep:star (loop ~parens:true)) ppf ts
    | Ptyp_constr (ts, constr) ->
      Fmt.(
        pf ppf "%a@;%s" (parens (list ~sep:comma (loop ~parens:true))) ts constr)
    | Ptyp_variant row -> Fmt.pf ppf "@[[@;%a@;]@]" pp_row row
    | Ptyp_mu (x, t) -> Fmt.pf ppf "@[mu '%s.@;%a@]" x pp_core_type t
    | Ptyp_where (t1, x, t2) ->
      Fmt.pf ppf "@[%a@;where@;%s@;=@;%a@]" pp_core_type t1 x pp_core_type t2
  in
  loop ppf core_type


and pp_row ppf (row_fields, closed_flag) =
  let closed_flag =
    match closed_flag with
    | Closed -> "<"
    | Open -> ">"
  in
  Fmt.(pf ppf "%s@;%a" closed_flag (list ~sep:vbar pp_row_field) row_fields)


and pp_row_field ppf (Row_tag (tag, core_type)) =
  Fmt.(pf ppf "%s%a" tag (option (any "@;of@;" ++ pp_core_type)) core_type)


let pp_core_scheme ppf (variables, core_type) =
  Fmt.(
    pf
      ppf
      "@[%a@;.@;%a@]"
      (list ~sep:comma string)
      variables
      pp_core_type
      core_type)


let rec pp_pattern ppf pattern =
  match pattern with
  | Ppat_any -> Fmt.pf ppf "_"
  | Ppat_var x -> Fmt.pf ppf "%s" x
  | Ppat_alias (pat, x) -> Fmt.pf ppf "@[%a@;as@;%s@]" pp_pattern pat x
  | Ppat_const const -> Fmt.pf ppf "%s" (string_of_constant const)
  | Ppat_tuple ts -> Fmt.(pf ppf "@[(%a)@]" (list ~sep:comma pp_pattern) ts)
  | Ppat_construct (constr, pat) ->
    Fmt.(
      pf ppf "@[%s%a@]" constr (option (sp ++ pp_pattern)) Option.(pat >>| snd))
  | Ppat_constraint (pat, core_type) ->
    Fmt.pf ppf "@[(%a@;:@;%a)@]" pp_pattern pat pp_core_type core_type
  | Ppat_variant (tag, pat) ->
    Fmt.(pf ppf "@[`%s%a@]" tag (option (sp ++ pp_pattern)) pat)


let pp_let_bindings ?(flag = "") ~pp ppf bindings =
  match bindings with
  | [] -> ()
  | [ b ] -> Fmt.pf ppf "@[let %s%a@]" flag pp b
  | b :: bs ->
    Fmt.(pf ppf "@[<v>let %s%a@,%a@]" flag pp b (list ~sep:(any "@,and") pp) bs)


let rec pp_expression ppf exp =
  match exp with
  | Pexp_var x -> Fmt.pf ppf "%s" x
  | Pexp_prim prim -> Fmt.pf ppf "%%prim %s" (string_of_primitive prim)
  | Pexp_const const -> Fmt.pf ppf "%s" (string_of_constant const)
  | Pexp_fun (pat, exp) ->
    Fmt.pf ppf "@[fun@;%a->@;%a@]" pp_pattern pat pp_expression exp
  | Pexp_app (exp1, exp2) ->
    Fmt.pf ppf "@[%a@ %a@]" pp_expression exp1 pp_expression exp2
  | Pexp_let (rec_flag, value_bindings, exp) ->
    let flag =
      match rec_flag with
      | Nonrecursive -> ""
      | Recursive -> "rec "
    in
    Fmt.pf
      ppf
      "@[%a in@;%a@]"
      (fun ppf -> pp_let_bindings ~flag ~pp:pp_value_binding ppf)
      value_bindings
      pp_expression
      exp
  | Pexp_forall (variables, exp) ->
    Fmt.(
      pf
        ppf
        "@[forall@;%a->@;%a@]"
        (list ~sep:comma string)
        variables
        pp_expression
        exp)
  | Pexp_exists (variables, exp) ->
    Fmt.(
      pf
        ppf
        "@[exists@;%a->@;%a@]"
        (list ~sep:comma string)
        variables
        pp_expression
        exp)
  | Pexp_construct (constr, exp) ->
    Fmt.(pf ppf "@[%s%a@]" constr (option (sp ++ pp_expression)) exp)
  | Pexp_constraint (exp, core_type) ->
    Fmt.pf ppf "@[(%a@;:@;%a)@]" pp_expression exp pp_core_type core_type
  | Pexp_record label_exps ->
    let pp_label_exp ppf (label, exp) =
      Fmt.pf ppf "@[%s@;=@;%a@]" label pp_expression exp
    in
    Fmt.(pf ppf "@[{%a}@]" (list ~sep:comma pp_label_exp) label_exps)
  | Pexp_field (exp, label) -> Fmt.pf ppf "@[%a.%s@]" pp_expression exp label
  | Pexp_tuple exps ->
    Fmt.(pf ppf "@[(%a)@]" (list ~sep:comma pp_expression) exps)
  | Pexp_match (exp, cases) ->
    Fmt.(
      pf
        ppf
        "@[<hv>@[@[match@ %a@]@ with@]@ (%a)@]"
        pp_expression
        exp
        (list ~sep:vbar pp_case)
        cases)
  | Pexp_ifthenelse (exp1, exp2, exp3) ->
    Fmt.pf
      ppf
      "@[(@[if@ %a@]@;@[then@ %a@]@;@[else@ %a@])@]"
      pp_expression
      exp1
      pp_expression
      exp2
      pp_expression
      exp3
  | Pexp_try (exp, cases) ->
    Fmt.(
      pf
        ppf
        "@[<hv>@[@[try@ %a@]@ with@]@ (%a)@]"
        pp_expression
        exp
        (list ~sep:vbar pp_case)
        cases)
  | Pexp_sequence _ ->
    let rec loop exp =
      match exp with
      | Pexp_sequence (exp1, exp2) -> exp1 :: loop exp2
      | _ -> [ exp ]
    in
    Fmt.(pf ppf "@[<hv>%a@]" (list ~sep:semi pp_expression) (loop exp))
  | Pexp_while (exp1, exp2) ->
    Fmt.pf
      ppf
      "@[<2>while@;%a@;do@;%a@;done@]"
      pp_expression
      exp1
      pp_expression
      exp2
  | Pexp_for (pat, exp1, exp2, direction_flag, exp3) ->
    Fmt.pf
      ppf
      "@[<hv0>@[<hv2>@[<2>for %a =@;%a@;%s@;%a@;do@]@;%a@]@;done@]"
      pp_pattern
      pat
      pp_expression
      exp1
      (string_of_direction_flag direction_flag)
      pp_expression
      exp2
      pp_expression
      exp3
  | Pexp_variant (tag, exp) ->
    Fmt.(pf ppf "@[`%s%a@]" tag (option (sp ++ pp_expression)) exp)


and pp_expression_function ppf exp =
  match exp with
  | Pexp_fun (pat, exp) ->
    Fmt.pf ppf "%a@ %a" pp_pattern pat pp_expression_function exp
  | _ -> Fmt.pf ppf "=@;%a" pp_expression exp


and pp_value_binding ppf nonrec_value_binding =
  let pat = nonrec_value_binding.pvb_pat
  and exp = nonrec_value_binding.pvb_expr in
  match pat with
  | Ppat_var x -> Fmt.pf ppf "@[%s@ %a@]" x pp_expression_function exp
  | _ -> Fmt.pf ppf "@[%a@;=@;%a@]" pp_pattern pat pp_expression exp


and pp_case ppf case =
  Fmt.pf ppf "@[%a@;->@;%a@]" pp_pattern case.pc_lhs pp_expression case.pc_rhs


let pp_constructor_argument ppf constr_arg =
  Fmt.(
    pf
      ppf
      "@[of@;%a%a%a@]"
      (list ~sep:sp string)
      constr_arg.pconstructor_arg_betas
      (if List.is_empty constr_arg.pconstructor_arg_betas
       then nop
       else any ".@;")
      ()
      pp_core_type
      constr_arg.pconstructor_arg_type)


let pp_constraints ppf constraints =
  let pp_constraint ppf (t1, t2) =
    Fmt.pf ppf "@[%a@;=@;%a@]" pp_core_type t1 pp_core_type t2
  in
  if List.is_empty constraints
  then ()
  else
    Fmt.(
      pf
        ppf
        "constraint@;%a"
        (list ~sep:(any "@;and@;") pp_constraint)
        constraints)


let pp_constructor_declaration ppf constr_decl =
  Fmt.(
    pf
      ppf
      "@[%s%a%a@]"
      constr_decl.pconstructor_name
      (option (sp ++ pp_constructor_argument))
      constr_decl.pconstructor_arg
      pp_constraints
      constr_decl.pconstructor_constraints)


let pp_label_declaration ppf label_decl =
  Fmt.(
    pf
      ppf
      "@[%s@;:@;%a%a%a@]"
      label_decl.plabel_name
      (list ~sep:sp string)
      label_decl.plabel_betas
      (if List.is_empty label_decl.plabel_betas then nop else any ".@;")
      ()
      pp_core_type
      label_decl.plabel_arg)


let pp_type_decl_kind ppf type_decl_kind =
  match type_decl_kind with
  | Ptype_variant constr_decls ->
    Fmt.(
      pf
        ppf
        "@;=@;@[<hv>%a@]"
        (list ~sep:vbar pp_constructor_declaration)
        constr_decls)
  | Ptype_record label_decls ->
    Fmt.(
      pf
        ppf
        "@;=@;@[<hv>{@;%a@;}@]"
        (list ~sep:(any "@;;@;") pp_label_declaration)
        label_decls)
  | Ptype_abstract -> ()
  | Ptype_alias core_type -> Fmt.pf ppf "@;=@;%a" pp_core_type core_type
  | Ptype_open -> Fmt.pf ppf "@;=@;.."


let pp_type_params ppf params =
  match params with
  | [] -> ()
  | [ param ] -> Fmt.pf ppf "%s@;" param
  | params -> Fmt.(parens (list ~sep:comma string) ++ sp) ppf params


let pp_type_declaration ppf type_decl =
  Fmt.pf
    ppf
    "@[<hv>@[type@;%a%s@]%a@]"
    pp_type_params
    type_decl.ptype_params
    type_decl.ptype_name
    pp_type_decl_kind
    type_decl.ptype_kind


let pp_extension_constructor_kind ppf ext_constr_kind =
  match ext_constr_kind with
  | Pext_decl constr_decl -> pp_constructor_declaration ppf constr_decl


let pp_extension_constructor ppf ext_constr =
  pp_extension_constructor_kind ppf ext_constr.pext_kind


let pp_extension_constructors ppf ext_constrs =
  Fmt.(
    pf
      ppf
      "@;=@;@[<hv>%a@]"
      (list ~sep:vbar pp_extension_constructor)
      ext_constrs)


let pp_type_exception ppf { ptyexn_constructor = exn_constr } =
  Fmt.pf
    ppf
    "@[exception@;%a]"
    pp_extension_constructor_kind
    exn_constr.pext_kind


let pp_type_declarations ~pp ppf bindings =
  match bindings with
  | [] -> ()
  | [ b ] -> Fmt.pf ppf "@[type %a@]" pp b
  | b :: bs ->
    Fmt.(pf ppf "@[<v>type %a@,%a@]" pp b (list ~sep:(any "@,and") pp) bs)


let pp_structure_item ppf str_item =
  match str_item with
  | Pstr_value (rec_flag, value_bindings) ->
    let flag =
      match rec_flag with
      | Nonrecursive -> ""
      | Recursive -> "rec "
    in
    pp_let_bindings ~flag ~pp:pp_value_binding ppf value_bindings
  | Pstr_primitive value_desc ->
    Fmt.pf
      ppf
      "@[external@;%s@;:@;%a@;=@;%s@]"
      value_desc.pval_name
      pp_core_scheme
      value_desc.pval_type
      value_desc.pval_prim
  | Pstr_type type_decls ->
    let pp_type_declaration ppf type_decl =
      Fmt.pf
        ppf
        "@[<hv>@[%a%s@]@;=@;%a@]"
        pp_type_params
        type_decl.ptype_params
        type_decl.ptype_name
        pp_type_decl_kind
        type_decl.ptype_kind
    in
    pp_type_declarations ~pp:pp_type_declaration ppf type_decls
  | Pstr_exception exn -> pp_type_exception ppf exn
  | Pstr_typext type_ext ->
    Fmt.pf
      ppf
      "@[<hv>@[%a%s@]@;=@;%a@]"
      pp_type_params
      type_ext.ptyext_params
      type_ext.ptyext_name
      pp_extension_constructors
      type_ext.ptyext_constructors


let pp_structure ppf str = Fmt.(list ~sep:(any "@.") pp_structure_item) ppf str
