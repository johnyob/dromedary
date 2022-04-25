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

module Type_var = struct
  module T = struct
    type t = Decoded.Var.t [@@deriving sexp_of]

    let compare t1 t2 = Int.compare (Decoded.Var.id t1) (Decoded.Var.id t2)
    let t_of_sexp _ = raise_s [%message "Var.t_of_sexp is not supported"]
  end

  include T
  include Comparable.Make (T)

  let make = Decoded.Var.make
  let id = Decoded.Var.id
  let decode t = t
end

module Type_expr = struct
  module T = struct
    type t = Decoded.Type.t [@@deriving sexp_of]

    and 'a desc =
      | Ttyp_var of Type_var.t
      | Ttyp_arrow of 'a * 'a
      | Ttyp_tuple of 'a list
      | Ttyp_constr of 'a type_constr
      | Ttyp_variant of 'a
      | Ttyp_row_cons of tag * 'a * 'a
      | Ttyp_row_uniform of 'a

    and 'a type_constr = 'a list * string

    let compare t1 t2 = Int.compare (Decoded.Type.id t1) (Decoded.Type.id t2)
    let t_of_sexp _ = raise_s [%message "Type_expr.t_of_sexp is not supported"]
  end

  include T
  include Comparable.Make (T)

  let make desc =
    let make = Decoded.Type.make in
    match desc with
    | Ttyp_var var -> make (Var var)
    | Ttyp_arrow (t1, t2) -> make (Former (Arrow (t1, t2)))
    | Ttyp_tuple ts -> make (Former (Tuple ts))
    | Ttyp_constr (ts, constr_name) -> make (Former (Constr (ts, constr_name)))
    | Ttyp_variant t -> make (Former (Variant t))
    | Ttyp_row_cons (tag, t1, t2) -> make (Row_cons (tag, t1, t2))
    | Ttyp_row_uniform t -> make (Row_uniform t)


  let desc_of_decoded_desc (decoded_desc : _ Decoded.Type.desc) =
    match decoded_desc with
    | Var var -> Ttyp_var var
    | Former (Arrow (t1, t2)) -> Ttyp_arrow (t1, t2)
    | Former (Tuple ts) -> Ttyp_tuple ts
    | Former (Constr (ts, constr_name)) -> Ttyp_constr (ts, constr_name)
    | Former (Variant t) -> Ttyp_variant t
    | Row_cons (tag, t1, t2) -> Ttyp_row_cons (tag, t1, t2)
    | Row_uniform t -> Ttyp_row_uniform t


  let desc type_expr = desc_of_decoded_desc (Decoded.Type.desc type_expr)
  let id t = Decoded.Type.id t
  let mu var t = Decoded.Type.mu var t
  let let_ ~binding ~in_ = Decoded.Type.let_ ~binding ~in_

  let fold t ~f ~mu ~var =
    Decoded.Type.fold
      ~f:(fun decoded_desc -> f (desc_of_decoded_desc decoded_desc))
      ~mu
      ~var
      t


  let decode t = t
end

type type_expr = Type_expr.t [@@deriving sexp_of]
type row = Type_expr.t [@@deriving sexp_of]
type type_var = Type_var.t [@@derving sexp_of]

let sexp_of_type_var = Type_var.sexp_of_t

type scheme = type_var list * type_expr [@@deriving sexp_of]

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
  | Type_open
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

let pp_type_expr_mach =
  let print ~indent ppf = Format.fprintf ppf "%sType expr: %s@." indent in
  let pp_type_expr_mach =
    Type_expr.fold
      ~f:(fun desc ~indent ppf ->
        let print = print ~indent ppf in
        let indent = indent_space ^ indent in
        match desc with
        | Ttyp_var var ->
          print (Format.asprintf "Variable: %d" (Type_var.id var))
        | Ttyp_arrow (t1, t2) ->
          print "Arrow";
          t1 ~indent ppf;
          t2 ~indent ppf
        | Ttyp_tuple ts ->
          print "Tuple";
          List.iter ~f:(fun t -> t ~indent ppf) ts
        | Ttyp_constr (ts, constr) ->
          print (Format.asprintf "Constructor: %s" constr);
          List.iter ~f:(fun t -> t ~indent ppf) ts
        | Ttyp_variant t ->
          print "Variant";
          t ~indent ppf
        | Ttyp_row_cons (label, t1, t2) ->
          print "Row cons";
          Format.fprintf ppf "%sLabel: %s@." indent label;
          t1 ~indent ppf;
          t2 ~indent ppf
        | Ttyp_row_uniform t ->
          print "Row uniform";
          t ~indent ppf)
      ~mu:(fun var t ~indent ppf ->
        print ~indent ppf "Mu";
        let indent = indent_space ^ indent in
        Format.fprintf ppf "%sVariable: %d@." indent (Type_var.id var);
        t ~indent ppf)
      ~var:(fun var ~indent ppf ->
        print ~indent ppf (Format.asprintf "Variable: %d" (Type_var.id var)))
  in
  fun ~indent ppf type_expr -> pp_type_expr_mach type_expr ~indent ppf


let pp_type_expr ppf type_expr =
  let rec loop ?(parens = false) ppf type_expr =
    match Type_expr.desc type_expr with
    | Ttyp_var var -> Format.fprintf ppf "%d" (Type_var.id var)
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
    (String.concat
       ~sep:" "
       (List.map
          ~f:(fun t -> Decoded.Var.id t |> Int.to_string)
          constr_arg.constructor_arg_betas));
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
    (String.concat
       ~sep:" "
       (List.map
          ~f:(fun t -> Decoded.Var.id t |> Int.to_string)
          constr_decl.constructor_alphas));
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
    (String.concat
       ~sep:" "
       (List.map
          ~f:(fun t -> Decoded.Var.id t |> Int.to_string)
          label_decl.label_alphas));
  Format.fprintf
    ppf
    "%sLabel betas: %s@."
    indent
    (String.concat
       ~sep:" "
       (List.map
          ~f:(fun t -> Decoded.Var.id t |> Int.to_string)
          label_decl.label_betas));
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
    (String.concat
       ~sep:" "
       (List.map
          ~f:(fun t -> Decoded.Var.id t |> Int.to_string)
          alias.alias_alphas));
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
  | Type_open -> print "Open"


let pp_type_declaration_mach ~indent ppf type_decl =
  Format.fprintf ppf "%sType declaration:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sType name: %s@." indent type_decl.type_name;
  pp_type_decl_kind_mach ~indent ppf type_decl.type_kind
