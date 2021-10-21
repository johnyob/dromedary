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

(** This module implements the constraint syntax. We make use of GADT 
    syntax to encode the type of the "constraint value". *)

open Intf

(* ------------------------------------------------------------------------- *)

module type S = sig
  (** Abstract types to be substituted by functor arguments. *)

  (** The type [term_var] is the term variables, given by the functor argument
      [Term_var]. *)

  type term_var

  (** The types [typ_var] and ['a typ_former] are the types of type variables
      and type formers (also known as type constructors), used in type 
      reconstruction. See {!Intf.Type_var} and {!Intf.Type_former}. *)

  type typ_var
  type 'a typ_former

  (** The types [typ] and [scheme] are concrete representations of types
      and type schemes. See {!Intf.Types}. *)

  type typ
  type scheme

  (* ----------------------------------------------------------------------- *)

  (** [variable] is the abstract type for constraint variables. *)

  type variable

  (** [fresh ()] creates a fresh constraint variable. *)

  val fresh : unit -> variable

  (* ----------------------------------------------------------------------- *)

  (** The [empty] type is used to for the encoded value of the 
      constraint [false]. *)

  type empty = |

  (** ['a t] is a constraint with value type ['a]. *)
  type _ t =
    | Cst_true : unit t (** [true] *)
    | Cst_false : empty t (** [false] *)
    (* Cst_conj : 'ts constraint_list -> 'ts t *)
    (* constraint_list = Dependent_list (struct type nonrec 'a t = 'a t).t *)
    | Cst_conj : 'a t * 'b t -> ('a * 'b) t (** [C1 && C2] *)
    | Cst_eq : variable * variable -> unit t (** [a1 = a2] *)
    | Cst_exist : variable * 'a t -> 'a t (** [exists a. C] *)
    | Cst_forall : variable * 'a t -> 'a t (** [forall a. C] *)
    | Cst_instance : term_var * variable -> typ list t (** [x <= a] *)
    | Cst_def : def_binding list * 'a t -> 'a t
        (** [def x1 : a1 and ... and xn : an in C] *)
    | Cst_let : 'a let_binding * 'b t -> ((term_var * scheme) * 'a bound * 'b) t
        (** [let b1 ... bn [C]. (x1 : b1 and ... xn : bn) in C']. *)
    | Cst_map : 'a t * ('a -> 'b) -> 'b t (** [map C f]. *)
    | Cst_match : 'a t * 'b case list -> ('a * 'b list) t
        (** [match C with (... | (x1 : a1 ... xn : an) -> Ci | ...)]. *)

  and binding =
    { cb_tevar : term_var
    ; cb_var : variable
    }

  and def_binding = binding

  and 'a let_binding =
    { clb_cst : 'a t
    ; clb_bs : binding list
    }

  and 'a bound = typ_var list * 'a t

  and 'a case =
    { ccase_bs : binding list
    ; ccase_cst : 'a t
    }
end

(* The type of the functor [Make]. *)

module type Make_S = functor (Term_var : Term_var) (Types : Types) ->
  S
    with type term_var := Term_var.t
     and type typ_var := Types.Var.t
     and type 'a typ_former := 'a Types.Former.t
     and type typ := Types.Type.t
     and type scheme := Types.scheme

(* ------------------------------------------------------------------------- *)

module type Intf = sig

  (* The functor [Make]. *)
  module Make : Make_S

end