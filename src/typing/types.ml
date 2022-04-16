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
open Util.Pretty_printer

type tag = string [@@deriving sexp_of]

module Var = struct
  module T = struct
    type t = Decoded.Var.t [@@deriving sexp_of]

    let compare t1 t2 = Int.compare (Decoded.Var.id t1) (Decoded.Var.id t2)
    let t_of_sexp _ = Decoded.Var.make ()
  end

  include T
  include Comparable.Make (T)

  let make = Decoded.Var.make
  let id = Decoded.Var.id
end

type type_var = Var.t [@@deriving sexp_of]

type type_expr = Decoded.Type.t [@@deriving sexp_of]

and type_desc =
  | Ttyp_var
  | Ttyp_arrow of type_expr * type_expr
  | Ttyp_tuple of type_expr list
  | Ttyp_constr of type_constr
  | Ttyp_variant of type_expr
  | Ttyp_row_cons of tag * type_expr * row
  | Ttyp_row_uniform of type_expr

and row = type_expr
and type_constr = type_expr list * string [@@deriving sexp_of]
and scheme = type_var list * type_expr [@@deriving sexp_of]

let make (desc' : type_desc) =
  let open Decoded.Type in
  match desc' with
  | Ttyp_var -> var ()
  | Ttyp_arrow (t1, t2) -> former (Arrow (t1, t2))
  | Ttyp_tuple ts -> former (Tuple ts)
  | Ttyp_constr (ts, constr_name) -> former (Constr (ts, constr_name))
  | Ttyp_variant t -> former (Variant t)
  | Ttyp_row_cons (tag, t1, t2) -> row_cons tag t1 t2
  | Ttyp_row_uniform t -> row_uniform t


let desc type_expr =
  match Decoded.Type.desc type_expr with
  | Var -> Ttyp_var
  | Former (Arrow (t1, t2)) -> Ttyp_arrow (t1, t2)
  | Former (Tuple ts) -> Ttyp_tuple ts
  | Former (Constr (ts, constr_name)) -> Ttyp_constr (ts, constr_name)
  | Former (Variant t) -> Ttyp_variant t
  | Row_cons (tag, t1, t2) -> Ttyp_row_cons (tag, t1, t2)
  | Row_uniform t -> Ttyp_row_uniform t


let id t = Decoded.Type.id t
let of_var var = Decoded.Type.of_var var
let to_var = Decoded.Type.to_var

(* Type definitions *)

type type_declaration =
  { type_name : string
  ; type_kind : type_decl_kind
  }
[@@deriving sexp_of]

and type_decl_kind =
  | Type_record of label_declaration list
  | Type_variant of constructor_declaration list
  | Type_abstract
  | Type_alias of alias
[@@deriving sexp_of]

and alias =
  { alias_alphas : type_var list
  ; alias_name : string
  ; alias_type : type_expr
  }
[@@deriving sexp_of]

and label_declaration =
  { label_name : string
  ; label_alphas : type_var list
  ; label_betas : type_var list
  ; label_arg : type_expr
  ; label_type : type_expr
  }
[@@deriving sexp_of]

and constructor_declaration =
  { constructor_name : string
  ; constructor_alphas : type_var list
  ; constructor_arg : constructor_argument option
  ; constructor_type : type_expr
  ; constructor_constraints : (type_expr * type_expr) list
  }
[@@deriving sexp_of]

and constructor_argument =
  { constructor_arg_betas : type_var list
  ; constructor_arg_type : type_expr
  }
[@@deriving sexp_of]

(* Constructor and record label descriptions *)

type constructor_description =
  { constructor_name : string
  ; constructor_arg : type_expr option
  ; constructor_type : type_expr
  }
[@@deriving sexp_of]

type variant_description =
  { variant_tag : tag
  ; variant_row : row
  }
[@@deriving sexp_of]

type label_description =
  { label_name : string
  ; label_arg : type_expr
  ; label_type : type_expr
  }
[@@deriving sexp_of]

let indent_space = "   "

let rec pp_type_expr_mach ~indent ppf type_expr =
  let print = Format.fprintf ppf "%sType expr: %s@." indent in
  let indent = indent_space ^ indent in
  match desc type_expr with
  | Ttyp_var ->
    print (Format.asprintf "Variable: %d" (Decoded.Type.id type_expr))
  | Ttyp_arrow (t1, t2) ->
    print "Arrow";
    pp_type_expr_mach ~indent ppf t1;
    pp_type_expr_mach ~indent ppf t2
  | Ttyp_tuple ts ->
    print "Tuple";
    List.iter ~f:(pp_type_expr_mach ~indent ppf) ts
  | Ttyp_constr (ts, constr) ->
    print (Format.asprintf "Constructor: %s" constr);
    List.iter ~f:(pp_type_expr_mach ~indent ppf) ts
  | Ttyp_variant t ->
    print "Variant";
    pp_type_expr_mach ~indent ppf t
  | Ttyp_row_cons (label, t1, t2) ->
    print "Row cons";
    Format.fprintf ppf "%sLabel: %s@." indent label;
    pp_type_expr_mach ~indent ppf t1;
    pp_type_expr_mach ~indent ppf t2
  | Ttyp_row_uniform t ->
    print "Row uniform";
    pp_type_expr_mach ~indent ppf t


let pp_type_expr ppf type_expr =
  let rec loop ?(parens = false) ppf type_expr =
    match desc type_expr with
    | Ttyp_var -> Format.fprintf ppf "%d" (Decoded.Type.id type_expr)
    | Ttyp_arrow (t1, t2) ->
      let pp ppf (t1, t2) =
        Format.fprintf
          ppf
          "@[%a@;->@;%a@]"
          (loop ~parens:true)
          t1
          (loop ~parens:false)
          t2
      in
      paren ~parens pp ppf (t1, t2)
    | Ttyp_tuple ts ->
      paren ~parens (list ~sep:"@;*@;" (loop ~parens:true)) ppf ts
    | Ttyp_constr (ts, constr) ->
      Format.fprintf
        ppf
        "%a@;%s"
        (list ~first:"(" ~last:")" ~sep:",@;" (loop ~parens:false))
        ts
        constr
    | Ttyp_variant t -> Format.fprintf ppf "@[[%a]@]" (loop ~parens:false) t
    | Ttyp_row_cons (label, t1, t2) ->
      Format.fprintf
        ppf
        "@[%s@;:@;%a@;|@;%a@]"
        label
        (loop ~parens:false)
        t1
        (loop ~parens:true)
        t2
    | Ttyp_row_uniform t -> Format.fprintf ppf "@[∂%a@]" (loop ~parens:true) t
  in
  loop ppf type_expr


let pp_constructor_description_mach ~indent ppf constr_desc =
  Format.fprintf ppf "%sConstructor description:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sName: %s@." indent constr_desc.constructor_name;
  let indent' = indent_space ^ indent in
  (match constr_desc.constructor_arg with
  | None -> ()
  | Some constr_arg ->
    Format.fprintf ppf "%sConstructor argument type:@." indent;
    pp_type_expr_mach ~indent:indent' ppf constr_arg);
  Format.fprintf ppf "%sConstructor type:@." indent;
  pp_type_expr_mach ~indent:indent' ppf constr_desc.constructor_type


let pp_variant_description_mach ~indent ppf variant_desc =
  Format.fprintf ppf "%sVariant description:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sTag: %s@." indent variant_desc.variant_tag;
  let indent' = indent_space ^ indent in
  Format.fprintf ppf "%sVariant row:@." indent;
  pp_type_expr_mach ~indent:indent' ppf variant_desc.variant_row


let pp_variant_description _ppf = assert false
let pp_constructor_description _ppf = assert false

let pp_label_description_mach ~indent ppf label_desc =
  Format.fprintf ppf "%sLabel description:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sLabel: %s@." indent label_desc.label_name;
  let indent' = indent_space ^ indent in
  Format.fprintf ppf "%sLabel argument type:@." indent;
  pp_type_expr_mach ~indent:indent' ppf label_desc.label_arg;
  Format.fprintf ppf "%sLabel type:@." indent;
  pp_type_expr_mach ~indent:indent' ppf label_desc.label_type


let pp_label_description _ppf = assert false

let pp_constraint_mach ~indent ppf (lhs, rhs) =
  Format.fprintf ppf "%sConstraint:@." indent;
  let indent = indent_space ^ indent in
  pp_type_expr_mach ~indent ppf lhs;
  pp_type_expr_mach ~indent ppf rhs


let pp_constructor_argument_mach ~indent ppf constr_arg =
  Format.fprintf ppf "%sConstructor argument:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf
    ppf
    "%sConstructor betas: %s@."
    indent
    (String.concat ~sep:" " (List.map ~f:(fun t -> Decoded.Var.id t |> Int.to_string) constr_arg.constructor_arg_betas));
  pp_type_expr_mach ~indent ppf constr_arg.constructor_arg_type


let pp_constructor_declaration_mach
    ~indent
    ppf
    (constr_decl : constructor_declaration)
  =
  Format.fprintf ppf "%sConstructor declaration:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf
    ppf
    "%sConstructor name: %s@."
    indent
    constr_decl.constructor_name;
  Format.fprintf
    ppf
    "%sConstructor alphas: %s@."
    indent
    (String.concat ~sep:" " (List.map ~f:(fun t -> Decoded.Var.id t |> Int.to_string) constr_decl.constructor_alphas));
  Format.fprintf ppf "%sConstructor type:@." indent;
  pp_type_expr_mach
    ~indent:(indent_space ^ indent)
    ppf
    constr_decl.constructor_type;
  (match constr_decl.constructor_arg with
  | None -> ()
  | Some constr_arg -> pp_constructor_argument_mach ~indent ppf constr_arg);
  List.iter
    ~f:(pp_constraint_mach ~indent ppf)
    constr_decl.constructor_constraints


let pp_label_declaration_mach ~indent ppf (label_decl : label_declaration) =
  Format.fprintf ppf "%sLabel declaration:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sLabel name: %s@." indent label_decl.label_name;
  Format.fprintf
    ppf
    "%sLabel alphas: %s@."
    indent
    (String.concat ~sep:" " (List.map ~f:(fun t -> Decoded.Var.id t |> Int.to_string) label_decl.label_alphas));
  Format.fprintf
    ppf
    "%sLabel betas: %s@."
    indent
    (String.concat ~sep:" " (List.map ~f:(fun t -> Decoded.Var.id t |> Int.to_string) label_decl.label_betas));
  pp_type_expr_mach ~indent ppf label_decl.label_arg;
  pp_type_expr_mach ~indent ppf label_decl.label_type


let pp_alias_mach ~indent ppf alias =
  Format.fprintf ppf "%sAlias@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sAlias name: %s@." indent alias.alias_name;
  Format.fprintf
    ppf
    "%sAlias alphas: %s@."
    indent
    (String.concat ~sep:" " (List.map ~f:(fun t -> Decoded.Var.id t |> Int.to_string) alias.alias_alphas));
  pp_type_expr_mach ~indent ppf alias.alias_type


let pp_type_decl_kind_mach ~indent ppf type_decl_kind =
  let print = Format.fprintf ppf "%sType declaration kind: %s@." indent in
  let indent = indent_space ^ indent in
  match type_decl_kind with
  | Type_variant constr_decls ->
    print "Variant";
    List.iter constr_decls ~f:(pp_constructor_declaration_mach ~indent ppf)
  | Type_record label_decls ->
    print "Record";
    List.iter label_decls ~f:(pp_label_declaration_mach ~indent ppf)
  | Type_abstract -> print "Abstract"
  | Type_alias alias ->
    print "Alias";
    pp_alias_mach ~indent ppf alias


let pp_type_declaration_mach ~indent ppf type_decl =
  Format.fprintf ppf "%sType declaration:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sType name: %s@." indent type_decl.type_name;
  pp_type_decl_kind_mach ~indent ppf type_decl.type_kind
