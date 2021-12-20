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
[@@deriving sexp_of]

type core_scheme = string list * core_type [@@deriving sexp_of]

type pattern =
  | Ppat_any
  | Ppat_var of string
  | Ppat_alias of pattern * string
  | Ppat_const of constant
  | Ppat_tuple of pattern list
  | Ppat_construct of string * pattern option
  | Ppat_constraint of pattern * core_type
[@@deriving sexp_of]

type expression =
  | Pexp_var of string
  | Pexp_prim of primitive
  | Pexp_const of constant
  | Pexp_fun of pattern * expression
  | Pexp_app of expression * expression
  | Pexp_let of value_bindings * expression
  | Pexp_forall of string list * expression
  | Pexp_exists of string list * expression
  | Pexp_constraint of expression * core_type
  | Pexp_construct of string * expression option
  | Pexp_record of (string * expression) list
  | Pexp_field of expression * string
  | Pexp_tuple of expression list
  | Pexp_match of expression * case list
  | Pexp_ifthenelse of expression * expression * expression
[@@deriving sexp_of]

and value_bindings =
  | Recursive of rec_value_binding list
  | Nonrecursive of nonrec_value_binding list

(** [P = E]. *)
and nonrec_value_binding =
  { pnvb_pat : pattern
  ; pnvb_expr : expression
  }

(** [x = E] *)
and rec_value_binding =
  { prvb_var : string
  ; prvb_expr : expression
  }

(** [P -> E]. *)
and case =
  { pc_lhs : pattern
  ; pc_rhs : expression
  }

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

type 'a pp = Format.formatter -> 'a -> unit

let indent_space = "   "

let rec pp_core_type_mach ~indent ppf core_type =
  let print = Format.fprintf ppf "%sType: %s@." indent in
  let indent = indent_space ^ indent in
  match core_type with
  | Ptyp_var x ->
    print "Variable";
    Format.fprintf ppf "%sVariable: %s" indent x
  | Ptyp_arrow (t1, t2) ->
    print "Arrow";
    pp_core_type_mach ~indent ppf t1;
    pp_core_type_mach ~indent ppf t2
  | Ptyp_tuple ts ->
    print "Tuple";
    List.iter ~f:(pp_core_type_mach ~indent ppf) ts
  | Ptyp_constr (ts, constr) ->
    print "Constructor";
    Format.fprintf ppf "%sConstructor: %s" indent constr;
    List.iter ~f:(pp_core_type_mach ~indent ppf) ts


let pp_core_scheme_mach ~indent ppf (variables, core_type) =
  Format.fprintf ppf "%sScheme:@." indent;
  let indent = indent_space ^ indent in
  let variables =
    match variables with
    | [] -> "[]"
    | variables -> String.concat ~sep:"," variables
  in
  Format.fprintf ppf "%sVariables: %s@." indent variables;
  pp_core_type_mach ~indent ppf core_type


let rec pp_pattern_mach ~indent ppf pat =
  let print = Format.fprintf ppf "%sPattern: %s@." indent in
  let indent = indent_space ^ indent in
  match pat with
  | Ppat_any -> print "Any"
  | Ppat_var x -> print ("Variable: " ^ x)
  | Ppat_alias (pat, x) ->
    print "Alias";
    pp_pattern_mach ~indent ppf pat;
    Format.fprintf ppf "%sAs: %s@." indent x
  | Ppat_const const -> print ("Constant: %s" ^ string_of_constant const)
  | Ppat_tuple pats ->
    print "Tuple";
    List.iter ~f:(pp_pattern_mach ~indent ppf) pats
  | Ppat_construct (constr, pat) ->
    print "Construct";
    Format.fprintf ppf "%sConstructor: %s@." indent constr;
    (match pat with
    | None -> ()
    | Some pat -> pp_pattern_mach ~indent ppf pat)
  | Ppat_constraint (pat, core_type) ->
    print "Constraint";
    pp_pattern_mach ~indent ppf pat;
    pp_core_type_mach ~indent ppf core_type


let rec pp_expression_mach ~indent ppf exp =
  let print = Format.fprintf ppf "%sExpression: %s@." indent in
  let indent = indent_space ^ indent in
  match exp with
  | Pexp_var x -> print ("Variable: " ^ x)
  | Pexp_prim prim -> print ("Primitive: " ^ string_of_primitive prim)
  | Pexp_const const -> print ("Constant: " ^ string_of_constant const)
  | Pexp_fun (pat, exp) ->
    print "Function";
    pp_pattern_mach ~indent ppf pat;
    pp_expression_mach ~indent ppf exp
  | Pexp_app (exp1, exp2) ->
    print "Application";
    pp_expression_mach ~indent ppf exp1;
    pp_expression_mach ~indent ppf exp2
  | Pexp_let (value_bindings, exp) ->
    print "Let";
    pp_value_bindings_mach ~indent ppf value_bindings;
    pp_expression_mach ~indent ppf exp
  | Pexp_forall (variables, exp) ->
    print "Forall";
    let variables = String.concat ~sep:"," variables in
    Format.fprintf ppf "%sVariables: %s@." indent variables;
    pp_expression_mach ~indent ppf exp
  | Pexp_exists (variables, exp) ->
    print "Exists";
    let variables = String.concat ~sep:"," variables in
    Format.fprintf ppf "%sVariables: %s@." indent variables;
    pp_expression_mach ~indent ppf exp
  | Pexp_constraint (exp, core_type) ->
    print "Constraint";
    pp_expression_mach ~indent ppf exp;
    pp_core_type_mach ~indent ppf core_type
  | Pexp_construct (constr, exp) ->
    print "Construct";
    Format.fprintf ppf "%sConstructor: %s@." indent constr;
    (match exp with
    | None -> ()
    | Some exp -> pp_expression_mach ~indent ppf exp)
  | Pexp_record label_exps ->
    print "Record";
    List.iter ~f:(pp_label_exp_mach ~indent ppf) label_exps
  | Pexp_field (exp, label) ->
    print "Field";
    pp_expression_mach ~indent ppf exp;
    Format.fprintf ppf "%sLabel: %s@." indent label
  | Pexp_tuple exps ->
    print "Tuple";
    List.iter ~f:(pp_expression_mach ~indent ppf) exps
  | Pexp_match (exp, cases) ->
    print "Match";
    pp_expression_mach ~indent ppf exp;
    Format.fprintf ppf "%sCases:@." indent;
    List.iter ~f:(pp_case_mach ~indent:(indent_space ^ indent) ppf) cases
  | Pexp_ifthenelse (exp1, exp2, exp3) ->
    print "If";
    pp_expression_mach ~indent ppf exp1;
    pp_expression_mach ~indent ppf exp2;
    pp_expression_mach ~indent ppf exp3


and pp_value_bindings_mach ~indent ppf value_bindings =
  let print = Format.fprintf ppf "%sValue bindings: %s@." indent in
  let indent = indent_space ^ indent in
  match value_bindings with
  | Nonrecursive nonrec_value_bindings ->
    print "Nonrecursive";
    List.iter
      ~f:(pp_nonrec_value_binding_mach ~indent ppf)
      nonrec_value_bindings
  | Recursive rec_value_bindings ->
    print "Recursive";
    List.iter ~f:(pp_rec_value_binding_mach ~indent ppf) rec_value_bindings


and pp_label_exp_mach ~indent ppf (label, exp) =
  Format.fprintf ppf "%sLabel: %s@." indent label;
  let indent = indent_space ^ indent in
  pp_expression_mach ~indent ppf exp


and pp_nonrec_value_binding_mach ~indent ppf value_binding =
  Format.fprintf ppf "%sValue binding:@." indent;
  let indent = indent_space ^ indent in
  pp_pattern_mach ~indent ppf value_binding.pnvb_pat;
  pp_expression_mach ~indent ppf value_binding.pnvb_expr


and pp_rec_value_binding_mach ~indent ppf value_binding =
  Format.fprintf ppf "%sValue binding:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sVariable: %s@." indent value_binding.prvb_var;
  pp_expression_mach ~indent ppf value_binding.prvb_expr


and pp_case_mach ~indent ppf case =
  Format.fprintf ppf "%sCase:@." indent;
  let indent = indent_space ^ indent in
  pp_pattern_mach ~indent ppf case.pc_lhs;
  pp_expression_mach ~indent ppf case.pc_rhs


let to_pp_mach ~name ~pp ppf t =
  Format.fprintf ppf "%s:@." name;
  let indent = "└──" in
  pp ~indent ppf t


let pp_core_type_mach = to_pp_mach ~name:"Core type" ~pp:pp_core_type_mach
let pp_core_scheme_mach = to_pp_mach ~name:"Core scheme" ~pp:pp_core_scheme_mach
let pp_pattern_mach = to_pp_mach ~name:"Pattern" ~pp:pp_pattern_mach
let pp_expression_mach = to_pp_mach ~name:"Expression" ~pp:pp_expression_mach

let pp_value_bindings_mach =
  to_pp_mach ~name:"Value bindings" ~pp:pp_value_bindings_mach


let pp_nonrec_value_binding_mach =
  to_pp_mach ~name:"Nonrecursive value binding" ~pp:pp_nonrec_value_binding_mach


let pp_rec_value_binding_mach =
  to_pp_mach ~name:"Recursive value binding" ~pp:pp_rec_value_binding_mach


let pp_case_mach = to_pp_mach ~name:"Case" ~pp:pp_case_mach

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

type separator = (unit, Format.formatter, unit) format

let none : separator = ""

let paren ?(first = none) ?(last = none) ~parens ~pp ppf t =
  if parens
  then (
    Format.fprintf ppf "(";
    Format.fprintf ppf first;
    pp ppf t;
    Format.fprintf ppf last;
    Format.fprintf ppf ")")
  else pp ppf t


let list ?(sep = ("@ " : separator)) ?(first = none) ?(last = none) ~pp ppf ts =
  match ts with
  | [] -> ()
  | [ t ] -> pp ppf t
  | ts ->
    let rec loop ppf ts =
      match ts with
      | [] -> assert false
      | [ t ] -> pp ppf t
      | t :: ts ->
        pp ppf t;
        Format.fprintf ppf sep;
        loop ppf ts
    in
    Format.fprintf ppf first;
    loop ppf ts;
    Format.fprintf ppf last


let option ?(first = none) ?(last = none) ~pp ppf opt =
  match opt with
  | None -> ()
  | Some t ->
    Format.fprintf ppf first;
    pp ppf t;
    Format.fprintf ppf last


let pp_core_type ppf core_type =
  let rec loop ?(parens = false) ppf core_type =
    match core_type with
    | Ptyp_var x -> Format.fprintf ppf "%s" x
    | Ptyp_arrow (t1, t2) ->
      let pp ppf (t1, t2) =
        Format.fprintf
          ppf
          "@[%a@;->@;%a@]"
          (loop ~parens:true)
          t1
          (loop ~parens:false)
          t2
      in
      paren ~parens ~pp ppf (t1, t2)
    | Ptyp_tuple ts ->
      paren ~parens ~pp:(list ~sep:"@;*@;" ~pp:(loop ~parens:true)) ppf ts
    | Ptyp_constr (ts, constr) ->
      Format.fprintf
        ppf
        "%a@;%s"
        (list ~first:"(" ~last:")" ~sep:",@;" ~pp:(loop ~parens:false))
        ts
        constr
  in
  loop ppf core_type


let pp_core_scheme ppf (variables, core_type) =
  Format.fprintf
    ppf
    "@[%a@;.@;%a@]"
    (fun ppf -> list ~sep:",@;" ~pp:Format.pp_print_string ppf)
    variables
    pp_core_type
    core_type


(* TODO: Improve bracketing! *)

let rec pp_pattern ppf pattern =
  match pattern with
  | Ppat_any -> Format.fprintf ppf "_"
  | Ppat_var x -> Format.fprintf ppf "%s" x
  | Ppat_alias (pat, x) -> Format.fprintf ppf "@[%a@;as@;%s@]" pp_pattern pat x
  | Ppat_const const -> Format.fprintf ppf "%s" (string_of_constant const)
  | Ppat_tuple ts ->
    Format.fprintf
      ppf
      "@[(%a)@]"
      (fun ppf -> list ~sep:",@;" ~pp:pp_pattern ppf)
      ts
  | Ppat_construct (constr, pat) ->
    Format.fprintf
      ppf
      "@[%s%a@]"
      constr
      (fun ppf -> option ~first:"@;" ~pp:pp_pattern ppf)
      pat
  | Ppat_constraint (pat, core_type) ->
    Format.fprintf ppf "@[(%a@;:@;%a)@]" pp_pattern pat pp_core_type core_type


let rec pp_expression ppf exp =
  match exp with
  | Pexp_var x -> Format.fprintf ppf "%s" x
  | Pexp_prim prim -> Format.fprintf ppf "%%prim %s" (string_of_primitive prim)
  | Pexp_const const -> Format.fprintf ppf "%s" (string_of_constant const)
  | Pexp_fun (pat, exp) ->
    Format.fprintf ppf "@[fun@;%a->@;%a@]" pp_pattern pat pp_expression exp
  | Pexp_app (exp1, exp2) ->
    Format.fprintf ppf "@[%a@ %a@]" pp_expression exp1 pp_expression exp2
  | Pexp_let (value_bindings, exp) ->
    Format.fprintf
      ppf
      "@[%a in@;%a@]"
      pp_value_bindings
      value_bindings
      pp_expression
      exp
  | Pexp_forall (variables, exp) ->
    Format.fprintf
      ppf
      "@[forall@;%a->@;%a@]"
      (fun ppf -> list ~sep:",@;" ~pp:Format.pp_print_string ppf)
      variables
      pp_expression
      exp
  | Pexp_exists (variables, exp) ->
    Format.fprintf
      ppf
      "@[exists@;%a->@;%a@]"
      (fun ppf -> list ~sep:",@;" ~pp:Format.pp_print_string ppf)
      variables
      pp_expression
      exp
  | Pexp_construct (constr, exp) ->
    Format.fprintf
      ppf
      "@[%s%a@]"
      constr
      (fun ppf -> option ~first:"@;" ~pp:pp_expression ppf)
      exp
  | Pexp_constraint (exp, core_type) ->
    Format.fprintf
      ppf
      "@[(%a@;:@;%a)@]"
      pp_expression
      exp
      pp_core_type
      core_type
  | Pexp_record label_exps ->
    let pp ppf (label, exp) =
      Format.fprintf ppf "@[%s@;=@;%a@]" label pp_expression exp
    in
    Format.fprintf
      ppf
      "@[{%a}@]"
      (fun ppf -> list ~sep:",@;" ~pp ppf)
      label_exps
  | Pexp_field (exp, label) ->
    Format.fprintf ppf "@[%a.%s@]" pp_expression exp label
  | Pexp_tuple exps ->
    Format.fprintf
      ppf
      "@[(%a)@]"
      (fun ppf -> list ~sep:",@;" ~pp:pp_expression ppf)
      exps
  | Pexp_match (exp, cases) ->
    Format.fprintf
      ppf
      "@[<hv>@[@[match@ %a@]@ with@]@ (%a)@]"
      pp_expression
      exp
      (fun ppf -> list ~sep:"@;|@;" ~pp:pp_case ppf)
      cases
  | Pexp_ifthenelse (exp1, exp2, exp3) ->
    Format.fprintf
      ppf
      "@[(@[if@ %a@]@;@[then@ %a@]@;@[else@ %a@])@]"
      pp_expression
      exp1
      pp_expression
      exp2
      pp_expression
      exp3


and pp_value_bindings ppf value_bindings =
  let bindings ~flag ~pp ppf bindings =
    match bindings with
    | [] -> assert false
    | [ b ] -> Format.fprintf ppf "@[let %s%a@]" flag pp b
    | b :: bs ->
      Format.fprintf
        ppf
        "@[<v>let %s%a@,%a@]"
        flag
        pp
        b
        (fun ppf -> list ~sep:"@,and" ~pp ppf)
        bs
  in
  match value_bindings with
  | Recursive rec_value_bindings ->
    bindings ~flag:"rec " ~pp:pp_rec_value_binding ppf rec_value_bindings
  | Nonrecursive nonrec_value_bindings ->
    bindings ~flag:"" ~pp:pp_nonrec_value_binding ppf nonrec_value_bindings


and pp_expression_function ppf exp =
  match exp with
  | Pexp_fun (pat, exp) ->
    Format.fprintf ppf "%a@ %a" pp_pattern pat pp_expression_function exp
  | _ -> Format.fprintf ppf "=@;%a" pp_expression exp


and pp_nonrec_value_binding ppf nonrec_value_binding =
  let pat = nonrec_value_binding.pnvb_pat
  and exp = nonrec_value_binding.pnvb_expr in
  match pat with
  | Ppat_var x -> Format.fprintf ppf "@[%s@ %a@]" x pp_expression_function exp
  | _ -> Format.fprintf ppf "@[%a@;=@;%a@]" pp_pattern pat pp_expression exp


and pp_rec_value_binding ppf rec_value_binding =
  Format.fprintf
    ppf
    "@[%s@ %a@]"
    rec_value_binding.prvb_var
    pp_expression_function
    rec_value_binding.prvb_expr


and pp_case ppf case =
  Format.fprintf
    ppf
    "@[%a@;->@;%a@]"
    pp_pattern
    case.pc_lhs
    pp_expression
    case.pc_rhs
