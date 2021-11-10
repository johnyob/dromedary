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

(** This module implements the constraint syntax. We make use of GADT syntax to
    encode the type of the "constraint value". *)

open Misc
open Base
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

  (** The types [typ] and [scheme] are concrete representations of types and
      type schemes. See {!Intf.Types}. *)

  type typ
  type typ_scheme

  (* ----------------------------------------------------------------------- *)

  (** [variable] is the abstract type for constraint variables. *)

  type variable = int

  (* ----------------------------------------------------------------------- *)

  (** A concrete representation of types using constraint variables. It is the
      free monad of the functor [Type_former.t] with variables [variable].

      While previously, we have stated that such a construct is unweidly, using
      this provides a richer interface between constraints and the rest of the
      type checker.

      Moreover, this provides a nicer translation between constraints and
      "graphic types".

      Graphic type nodes consist of a "structure", either a variable of a type
      former (isomorphic to what we define below, given a mapping between
      constraint variables and graphic nodes.) *)

  module Type : sig
    type t =
      | Var of variable
      | Form of t typ_former

    val var : variable -> t
    val form : t typ_former -> t
  end

  (* ----------------------------------------------------------------------- *)

  (** The [empty] type is used to for the encoded value of the constraint
      [false]. *)

  type empty = |

  (** ['a t] is a constraint with value type ['a]. *)
  type _ t =
    | Cst_true : unit t (** [true] *)
    | Cst_false : empty t (** [false] *)
    | Cst_conj : 'a t * 'b t -> ('a * 'b) t (** [C1 && C2] *)
    | Cst_eq : Type.t * Type.t -> unit t (** [t1 = t2] *)
    | Cst_exist : 'n variables * 'a t -> 'a t (** [exists a. C] *)
    | Cst_forall : 'n variables * 'a t -> 'a t (** [forall a. C] *)
    | Cst_instance : term_var * Type.t -> typ list t (** [x <= t] *)
    | Cst_def : def_binding list * 'a t -> 'a t
        (** [def x1 : t1 and ... and xn : tn in C] *)
    | Cst_let :
        ('m, 'n, 'a) let_binding * 'b t
        -> (term_binding list * 'a bound * 'b) t
        (** [let a1 ... am [C]. (x1 : t1 and ... xk : tk) in C']. *)
    | Cst_map : 'a t * ('a -> 'b) -> 'b t (** [map C f]. *)
    | Cst_match : 'a t * 'b case list -> ('a * 'b list) t
        (** [match C with (... | (x1 : t1 ... xn : tn) -> Ci | ...)]. *)
    | Cst_decode : Type.t -> typ t

  and term_binding = term_var * typ_scheme

  and binding = term_var * Type.t

  and def_binding = binding

  and ('m, 'n, 'a) scheme =
    { csch_rigid_vars : 'm variables
    ; csch_flexible_vars : 'n variables
    ; csch_cst : 'a t
    }

  and ('m, 'n, 'a) let_binding =
    { clb_sch : ('m, 'n, 'a) scheme
    ; clb_bs : binding list
    }

  and 'a bound = typ_var list * 'a

  and 'a case =
    { ccase_bs : binding list
    ; ccase_cst : 'a t
    }

  and 'n variables = (variable, 'n) Sized_list.t

  (* ----------------------------------------------------------------------- *)

  (* ['a t] forms an applicative functor *)

  include Applicative.S with type 'a t := 'a t

  include Applicative.Let_syntax with type 'a t := 'a t

  (* ----------------------------------------------------------------------- *)

  (* Combinators *)

  val ( &~ ) : 'a t -> 'b t -> ('a * 'b) t
  val ( >> ) : 'a t -> 'b t -> 'b t
  val ( =~ ) : Type.t -> Type.t -> unit t
  val inst : term_var -> Type.t -> typ list t

  val decode : Type.t -> typ t

  (* ----------------------------------------------------------------------- *)

  (* Continuations, binders and quantifiers *)

  module Continuation : sig
    (** A continuation of the type [('a, 'b) cont] is a continuation for
        constraint computations.

        An example usage is binders: e.g. [exists]. However, we also use them
        for typing patterns, etc.

        As with standard continuations, they form a monadic structure. *)
    type nonrec ('a, 'b) t = ('a -> 'b t) -> 'b t

    include Monad.S2 with type ('a, 'b) t := ('a, 'b) t
  end

  (* [('n, 'a) binder] is a binder that binds ['n] variables. *)

  type ('n, 'a) binder = ('n variables, 'a) Continuation.t

  (* [('m, 'n, 'a) binder2] is the 2 kinded version of [binder], bindings ['m]
     and ['n] rigid and flexible variables, respectively. *)
  type ('m, 'n, 'a) binder2 = ('m variables * 'n variables, 'a) Continuation.t

  val exists : 'n Size.t -> ('n, 'a) binder
  val forall : 'n Size.t -> ('n, 'a) binder

  (* ----------------------------------------------------------------------- *)

  (* Environmental constraints *)

  val ( #= ) : term_var -> Type.t -> binding
  val def : def_binding list -> 'a t -> 'a t
  val scheme : 'm variables -> 'n variables -> 'a t -> ('m, 'n, 'a) scheme

  val let_
    :  'm Size.t
    -> 'n Size.t
    -> ('m variables * 'n variables -> 'a t)
    -> ('m variables * 'n variables -> def_binding list)
    -> 'b t
    -> (term_binding list * 'a bound * 'b) t
end

(* The type of the functor [Make]. *)

module type Make_S = functor (Term_var : Term_var) (Types : Types) ->
  S
    with type term_var := Term_var.t
     and type typ_var := Types.Var.t
     and type 'a typ_former := 'a Types.Former.t
     and type typ := Types.Type.t
     and type typ_scheme := Types.scheme

(* ------------------------------------------------------------------------- *)

module type Intf = sig
  (* The functor [Make]. *)
  module Make : Make_S
end