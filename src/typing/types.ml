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
open Util.Pretty_printer

type label = string [@@deriving sexp_of]

type type_expr =
  | Ttyp_var of string
  | Ttyp_arrow of type_expr * type_expr
  | Ttyp_tuple of type_expr list
  | Ttyp_constr of type_constr
  | Ttyp_alias of type_expr * string
  | Ttyp_variant of type_expr
  | Ttyp_row_cons of label * type_expr * type_expr
  | Ttyp_row_uniform of type_expr
[@@deriving sexp_of]

and type_constr = type_expr list * string [@@deriving sexp_of]

module Algebra = struct
  open Constraints.Module_types

  module Term_var = struct
    type t = string [@@deriving sexp_of, compare]
  end

  module Type_var = struct
    type t = string [@@deriving sexp_of]

    let of_int x = "α" ^ Int.to_string x
  end

  module Type_former = struct
    module T = struct
      type 'a t =
        | Arrow of 'a * 'a
        | Tuple of 'a list
        | Constr of 'a list * string
        | Variant of 'a
      [@@deriving sexp_of]

      let id t =
        match t with
        | Arrow _ -> 0
        | Tuple _ -> 1
        | Variant _ -> 2
        | Constr (_, constr) -> 3 + String.hash constr


      module Traverse (F : Applicative.S) = struct
        module Intf = struct
          module type S = sig end
        end

        module F = struct
          include F
          include Applicative.Make_let_syntax (F) (Intf) ()
        end

        open F

        let traverse t ~f =
          let open Let_syntax in
          match t with
          | Arrow (t1, t2) ->
            let%map t1 = f t1
            and t2 = f t2 in
            Arrow (t1, t2)
          | Tuple ts ->
            let%map ts = all (List.map ~f ts) in
            Tuple ts
          | Constr (ts, constr) ->
            let%map ts = all (List.map ~f ts) in
            Constr (ts, constr)
          | Variant t ->
            let%map t = f t in
            Variant t


        let traverse2 t1 t2 ~f =
          let open Let_syntax in
          let open List.Or_unequal_lengths in
          match t1, t2 with
          | Arrow (t11, t12), Arrow (t21, t22) ->
            `Ok
              (let%map t1 = f t11 t21
               and t2 = f t12 t22 in
               Arrow (t1, t2))
          | Tuple ts1, Tuple ts2 ->
            (match List.map2 ~f ts1 ts2 with
            | Ok ts ->
              `Ok
                (let%map ts = all ts in
                 Tuple ts)
            | Unequal_lengths -> `Unequal_structure)
          | Constr (ts1, constr1), Constr (ts2, constr2)
            when String.(constr1 = constr2) ->
            (match List.map2 ~f ts1 ts2 with
            | Ok ts ->
              `Ok
                (let%map ts = all ts in
                 Constr (ts, constr1))
            | Unequal_lengths -> `Unequal_structure)
          | Variant t1, Variant t2 ->
            `Ok
              (let%map t = f t1 t2 in
               Variant t)
          | _, _ -> `Unequal_structure
      end
    end

    include T
    include Type_former.Make (T)
  end

  module Type = struct
    type t = type_expr [@@deriving sexp_of]

    let var x = Ttyp_var x

    let former former =
      match former with
      | Type_former.Arrow (t1, t2) -> Ttyp_arrow (t1, t2)
      | Type_former.Tuple ts -> Ttyp_tuple ts
      | Type_former.Constr (ts, constr) -> Ttyp_constr (ts, constr)
      | Type_former.Variant t -> Ttyp_variant t


    let mu x t = Ttyp_alias (t, x)

    let row_cons (label, t1) t2 = Ttyp_row_cons (label, t1, t2)
    
    let row_uniform t = Ttyp_row_uniform t
  end

  module Types = struct
    module Label = String
    module Var = Type_var
    module Former = Type_former
    module Type = Type

    type scheme = Var.t list * Type.t
  end
end

(* Type definitions *)

type type_declaration =
  { type_name : string
  ; type_kind : type_decl_kind
  }
[@@deriving sexp_of]

and type_decl_kind =
  | Type_record of label_declaration list
  | Type_variant of constructor_declaration list
[@@deriving sexp_of]

and label_declaration =
  { label_name : string
  ; label_alphas : string list
  ; label_betas : string list
  ; label_arg : type_expr
  ; label_type : type_expr
  }
[@@deriving sexp_of]

and constructor_declaration =
  { constructor_name : string
  ; constructor_alphas : string list
  ; constructor_arg : constructor_argument option
  ; constructor_type : type_expr
  ; constructor_constraints : (type_expr * type_expr) list
  }
[@@deriving sexp_of]

and constructor_argument =
  { constructor_arg_betas : string list
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
    match type_expr with
    | Ttyp_var x -> Format.fprintf ppf "%s" x
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
    | Ttyp_alias (t, x) ->
      Format.fprintf ppf "@[%a@;as@;%s@]" (loop ~parens:false) t x
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
(* 
let to_pp_mach ~pp ~name ppf t =
  Format.fprintf ppf "%s:@." name;
  let indent = "└──" in
  pp ~indent ppf t


let pp_type_expr_mach = to_pp_mach ~pp:pp_type_expr_mach ~name:"Type expr"

let pp_constructor_description_mach =
  to_pp_mach ~pp:pp_constructor_description_mach ~name:"Constructor description"


let pp_label_description_mach =
  to_pp_mach ~pp:pp_label_description_mach ~name:"Label description" *)