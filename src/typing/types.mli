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

open Util

(** Representation of types and declarations  *)

type tag = string

type type_expr [@@deriving sexp_of]

type type_desc =
  | Ttyp_var of string 
      (** Type variables ['a]. *)
  | Ttyp_arrow of type_expr * type_expr 
      (** Function types [T1 -> T2]. *)
  | Ttyp_tuple of type_expr list 
      (** Product (or "tuple") types. *)
  | Ttyp_constr of type_constr 
      (** Type constructors. *)
  | Ttyp_mu of string * type_expr
      (** Alias, required for displaying equi-recursive types. *)
  | Ttyp_where of type_expr * string * type_expr
      (** Where, used for translation of core type to type expr 
          (may be used in future for explicit sharing :) ) *)
  | Ttyp_variant of type_expr 
      (** Polymorphic variant [ [ ... ] ] *)
  | Ttyp_row_cons of tag * type_expr * row 
      (** Row cons [< `A : T, row >] *)
  | Ttyp_row_uniform of type_expr 
      (** Uniform row [ ∂<T> ] *)
[@@deriving sexp_of]

and row = type_expr
and type_constr = type_expr list * string [@@deriving sexp_of]

and scheme = string list * type_expr [@@deriving sexp_of]


val make_type_expr : type_desc -> type_expr

val type_desc : type_expr -> type_desc

(** [pp_type_expr_mach ppf type_expr] pretty prints an explicit tree of the 
    type expression [type_expr]. *)
val pp_type_expr_mach : indent:string -> type_expr Pretty_printer.t

(** [pp_type_expr ppf type_expr] pretty prints the syntactic representation of the
    type expression [type_expr]. *)
val pp_type_expr : type_expr Pretty_printer.t

module Algebra : sig
  open Constraints.Module_types

  (** [Term_var] implements the abstract notion of variables in Dromedary's expressions
   (or "Terms"). *)
  module Term_var : Term_var with type t = string

  (** [Type_var] implements the abstract notion of type variables in Dromedary's types. *)
  module Type_var : Type_var with type t = string

  (** [Type_former] defines the various type formers for Dromedary's types.
   
       This notion of type former differs from that of our formal descriptions,
       since it describes:
       - Arrow types (or function types).
       - Tuple tuples.
       - Type constructors (or "Type formers" are referred to in the formalizations).
   *)
  module Type_former : sig
    type 'a t =
      | Arrow of 'a * 'a
      | Tuple of 'a list
      | Constr of 'a list * string
      | Variant of 'a
    [@@deriving sexp_of]

    include Type_former.S with type 'a t := 'a t
  end

  (** [Type] is the abstraction of Dromedary's types, [type_expr]. *)
  module Type :
    Type
      with type label := string
       and type variable := Type_var.t
       and type 'a former := 'a Type_former.t
       and type t = type_expr

  include
    Algebra
      with module Term_var := Term_var
       and type Types.Label.t = string
       and module Types.Var = Type_var
       and module Types.Former = Type_former
       and module Types.Type = Type
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
  | Type_abstract
  | Type_alias of alias
[@@deriving sexp_of]

and alias = 
  { alias_alphas : string list
  ; alias_name : string
  ; alias_type : type_expr
  }
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
