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

type 'a pp = Format.formatter -> 'a -> unit

type type_expr =
  | Ttyp_var of string
  | Ttyp_arrow of type_expr * type_expr
  | Ttyp_tuple of type_expr list
  | Ttyp_constr of type_constr
  | Ttyp_alias of type_expr * string
[@@deriving sexp_of]

and type_constr = type_expr list * string [@@deriving sexp_of]

let indent_space = "   "

let rec pp_type_expr_mach ~indent ppf type_expr =
  let print = Format.fprintf ppf "%sType expr: %s@." indent in
  let indent = indent_space ^ indent in
  match type_expr with
  | Ttyp_var x -> print (Format.asprintf "Variable: %s" x)
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
  | Ttyp_alias (t, x) ->
    print "As";
    pp_type_expr_mach ~indent ppf t;
    Format.fprintf ppf "%sVariable: %s@." indent x


let pp_type_expr_mach ppf type_expr =
  Format.fprintf ppf "Type expr:@.";
  let indent = "└──" in
  pp_type_expr_mach ~indent ppf type_expr


let pp_type_expr _ppf = assert false

module Algebra = struct
  module Term_var = struct
    type t = string [@@deriving sexp_of, compare]
  end

  module Type_var = struct
    type t = string [@@deriving sexp_of]

    let of_int x = "α" ^ Int.to_string x
  end

  module Type_former = struct
    type 'a t =
      | Arrow of 'a * 'a
      | Tuple of 'a list
      | Constr of 'a list * string
    [@@deriving sexp_of]

    let map t ~f =
      match t with
      | Arrow (t1, t2) ->
        let t1' = f t1 in
        let t2' = f t2 in
        Arrow (t1', t2')
      | Tuple ts -> Tuple (List.map ~f ts)
      | Constr (ts, constr) -> Constr (List.map ~f ts, constr)


    let iter t ~f = ignore (map t ~f : unit t)

    let fold t ~f ~init =
      match t with
      | Arrow (t1, t2) ->
        let init = f t1 init in
        let init = f t2 init in
        init
      | Tuple ts -> List.fold_right ~f ~init ts
      | Constr (ts, _) -> List.fold_right ~f ~init ts


    exception Iter2

    let iter2_exn t1 t2 ~f =
      let list_iter2 xs ys ~f =
        (* Catch the [Base] exception and re-raise our exception *)
        try List.iter2_exn xs ys ~f with
        | _ -> raise Iter2
      in
      match t1, t2 with
      | Arrow (t11, t12), Arrow (t21, t22) ->
        f t11 t21;
        f t12 t22
      | Tuple ts1, Tuple ts2 -> list_iter2 ts1 ts2 ~f
      | Constr (ts1, constr1), Constr (ts2, constr2)
        when String.equal constr1 constr2 -> list_iter2 ts1 ts2 ~f
      | _, _ -> raise Iter2
  end

  module Type = struct

    type t = type_expr [@@deriving sexp_of]

    let var x = Ttyp_var x

    let former former =
      match former with
      | Type_former.Arrow (t1, t2) -> Ttyp_arrow (t1, t2)
      | Type_former.Tuple ts -> Ttyp_tuple ts
      | Type_former.Constr (ts, constr) -> Ttyp_constr (ts, constr)


    let mu x t = Ttyp_alias (t, x)
  end

  module Types = struct
    module Var = Type_var
    module Former = Type_former
    module Type = Type

    type scheme = Var.t list * Type.t
  end
end

(* Type definitions *)

type type_declaration =
  { type_name : string
  ; type_params : string list
  ; type_kind : type_decl_kind
  }

and type_decl_kind =
  | Type_record of label_declaration list
  | Type_variant of constructor_declaration list

and label_declaration =
  { label_name : string
  ; label_type_params : string list
  ; label_arg : type_expr
  ; label_type : type_expr
  }

and constructor_declaration =
  { constructor_name : string
  ; constructor_type_params : string list
  ; constructor_arg : type_expr option
  ; constructor_type : type_expr
  }

(* Constructor and record label descriptions *)

type constructor_description =
  { constructor_name : string
  ; constructor_arg : type_expr option
  ; constructor_type : type_expr
  }

type label_description =
  { label_name : string
  ; label_arg : type_expr
  ; label_type : type_expr
  }

(* 
let pp_constructor_description ~indent ppf constr_desc =
  Format.fprintf ppf "%sConstructor description:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sName: %s@." indent constr_desc.constructor_name;
  let indent' = indent_space ^ indent in
  (match constr_desc.constructor_arg with
  | None -> ()
  | Some constr_arg ->
    Format.fprintf ppf "%sConstructor argument type:@." indent;
    pp_type_expr ~indent:indent' ppf constr_arg);
  Format.fprintf ppf "%sConstructor type:@." indent;
  pp_type_expr ~indent:indent' ppf constr_desc.constructor_type


let pp_label_description ~indent ppf label_desc =
  Format.fprintf ppf "%sLabel description:@." indent;
  let indent = indent_space ^ indent in
  Format.fprintf ppf "%sLabel: %s@." indent label_desc.label_name;
  let indent' = indent_space ^ indent in
  Format.fprintf ppf "%sLabel argument type:@." indent;
  pp_type_expr ~indent:indent' ppf label_desc.label_arg;
  Format.fprintf ppf "%sLabel type:@." indent;
  pp_type_expr ~indent:indent' ppf label_desc.label_type *)
