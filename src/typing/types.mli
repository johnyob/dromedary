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
open Util


(** Representation of types and declarations  *)

type tag = string

module Var : sig
  type t = Decoded.Var.t [@@deriving sexp_of]
  include Comparable with type t := t
  
  val make : unit -> t
  val id : t -> int
end

type type_var = Var.t [@@deriving sexp_of]

type type_expr = Decoded.Type.t [@@deriving sexp_of]

type type_desc =
  | Ttyp_var
      (** Type variables ['a]. *)
  | Ttyp_arrow of type_expr * type_expr 
      (** Function types [T1 -> T2]. *)
  | Ttyp_tuple of type_expr list 
      (** Product (or "tuple") types. *)
  | Ttyp_constr of type_constr 
      (** Type constructors. *)
  | Ttyp_variant of type_expr 
      (** Polymorphic variant [ [ ... ] ] *)
  | Ttyp_row_cons of tag * type_expr * row 
      (** Row cons [< `A : T, row >] *)
  | Ttyp_row_uniform of type_expr 
      (** Uniform row [ ∂<T> ] *)
[@@deriving sexp_of]

and row = type_expr
and type_constr = type_expr list * string [@@deriving sexp_of]

and scheme = type_var list * type_expr [@@deriving sexp_of]


val make : type_desc -> type_expr
val desc : type_expr -> type_desc
val id : type_expr -> int
val of_var : type_var -> type_expr
val to_var : type_expr -> type_var option


(** [pp_type_expr_mach ppf type_expr] pretty prints an explicit tree of the 
    type expression [type_expr]. *)
val pp_type_expr_mach : indent:string -> type_expr Pretty_printer.t

(** [pp_type_expr ppf type_expr] pretty prints the syntactic representation of the
    type expression [type_expr]. *)
val pp_type_expr : type_expr Pretty_printer.t


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

val pp_constructor_declaration_mach
  :  indent:string
  -> constructor_declaration Pretty_printer.t

val pp_type_declaration_mach 
  :  indent:string 
  -> type_declaration Pretty_printer.t

(* Constructor and record label descriptions *)

type constructor_description =
  { constructor_name : string
  ; constructor_arg : type_expr option
  ; constructor_type : type_expr
  }
[@@deriving sexp_of]

val pp_constructor_description_mach
  :  indent:string
  -> constructor_description Pretty_printer.t

val pp_constructor_description : constructor_description Pretty_printer.t

type variant_description =
  { variant_tag : tag
  ; variant_row : row
  }
[@@deriving sexp_of]

val pp_variant_description_mach
  :  indent:string
  -> variant_description Pretty_printer.t

val pp_variant_description : variant_description Pretty_printer.t

type label_description =
  { label_name : string
  ; label_arg : type_expr
  ; label_type : type_expr
  }
[@@deriving sexp_of]

val pp_label_description_mach
  :  indent:string
  -> label_description Pretty_printer.t

val pp_label_description : label_description Pretty_printer.t
