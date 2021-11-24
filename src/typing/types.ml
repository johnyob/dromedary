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


open Base

(* ------------------------------------------------------------------------- *)

(** Representation of types and declarations  *)

type type_expr =
  | Ttyp_var of string
  (** Type variables ['a]. *)
  | Ttyp_arrow of type_expr * type_expr
  (** Function types [T1 -> T2]. *)
  | Ttyp_tuple of type_expr list
  (** Product (or "tuple") types. *)
  | Ttyp_constr of type_constr
  (** Type constructors. *)
  [@@deriving sexp_of]

and type_constr = type_expr list * string

(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)

(* Constructor and record label descriptions *)

type constructor_description = 
  { constructor_name : string
  ; constructor_arg  : type_expr option
  ; constructor_type : type_expr
  }

type label_description = 
  { label_name : string
  ; label_arg  : type_expr
  ; label_type : type_expr
  }