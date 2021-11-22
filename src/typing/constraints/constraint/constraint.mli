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

(** This module implements the constraint syntax. *)

open! Import
module Module_types = Module_types
open Module_types

(** The [Make] functor defines the constraint syntax, parameterized
    by the Algebra.  *)

module Make (Algebra : Algebra) : sig
  open Algebra
  module Type_var := Types.Var
  module Type_former := Types.Former

  (** [variable] is the type for constraint "type" variables. *)

  type variable = private int

  (** [fresh ()] creates a fresh constraint variable. *)

  val fresh : unit -> variable

  (** A concrete representation of types using constraint variables. It is the
      free monad of the functor [Type_former.t] with variables [variable].

      While previously, we have stated that such a construct is unweidly, using
      this provides a richer interface between constraints and the rest of the
      type checker.

      Moreover, this provides a nicer translation between constraints and
      "graphic types".

      Graphic type nodes consist of a "structure", either a variable of a type
      former (isomorphic to what we define below, given a mapping between
      constraint variables and graphic nodes.) 
  *)

  module Type : sig
    type t =
      | Var of variable
      | Form of t Type_former.t

    (** [var 'a] is the representation of the type variable ['a] as the 
        type [t]. See [Var] above. *)
    val var : variable -> t

    (** [form f] is the representation of the concrete type former [f] in
        type [t]. See [Form] above. *)
    val form : t Type_former.t -> t
  end

  (** ['a t] is a constraint with value type ['a]. 
          
      In the meta-theory, the constraint language has a defined type
      system. 
      
      In our implementation, we use GADTs to implement the 
      type system, where the type parameter ['a] denotes the type of 
      the constraint. 
  *)

  type _ t =
    | Cst_true : unit t (** [true] *)
    | Cst_conj : 'a t * 'b t -> ('a * 'b) t (** [C1 && C2] *)
    | Cst_eq : Type.t * Type.t -> unit t (** [t1 = t2] *)
    | Cst_exist : variable list * 'a t -> 'a t (** [exists a. C] *)
    | Cst_forall : variable list * 'a t -> 'a t (** [forall a. C] *)
    | Cst_instance : Term_var.t * Type.t -> Types.Type.t list t (** [x <= t] *)
    | Cst_def : binding list * 'a t -> 'a t
        (** [def x1 : t1 and ... and xn : tn in C] *)
    | Cst_let : 'a scheme * 'b t -> (term_binding list * 'a bound * 'b) t
        (** [let a1 ... am [C]. (x1 : t1 and ... xk : tk) in C']. *)
    | Cst_map : 'a t * ('a -> 'b) -> 'b t (** [map C f]. *)
    | Cst_match : 'a t * 'b case list -> ('a * 'b list) t
        (** [match C with (... | (x1 : t1 ... xn : tn) -> Ci | ...)]. *)
    | Cst_decode : Type.t -> Types.Type.t t (** [decode t] *)

  and term_binding = Term_var.t * Types.scheme

  and binding = Term_var.t * Type.t

  and 'a scheme =
    { csch_rigid_vars : variable list
    ; csch_flexible_vars : variable list
    ; csch_cst : 'a t
    ; csch_bindings : binding list
    }

  and 'a bound = Type_var.t list * 'a

  and 'a case =
    { ccase_bs : binding list
    ; ccase_cst : 'a t
    }

  (** ['a t] forms an applicative functor, allowing us to combine
      many constraints into a single one using [let%map]:

      {[
        val pat : Typedtree.pattern Constraint.t
        val exp : Typedtree.expression Constraint.t

        let%map pat and exp in
        Texp_fun (pat, ..., exp)
      ]}  
  *)

  include Applicative.S with type 'a t := 'a t
  include Applicative.Let_syntax with type 'a t := 'a t

  (* Combinators *)

  (** [&~] is an infix alias for [both]. *)
  val ( &~ ) : 'a t -> 'b t -> ('a * 'b) t

  (** [c1 >> c2 >> ... >> cn] solves [c1, ..., cn] yielding the value 
      of [cn]. It is the monodial operator of constraints. *)
  val ( >> ) : 'a t -> 'b t -> 'b t

  (** [t =~ t'] is an infix alias for [Cst_eq], denoting the equality
      constraint on types. *)
  val ( =~ ) : Type.t -> Type.t -> unit t

  (** [inst x t] is the constraint that instantiates [x] to [t].
      It returns the type variable substitution. *)
  val inst : Term_var.t -> Type.t -> Types.Type.t list t

  (** [decode t] is a constraint that evaluates to the decoded
      type of [t]. *)
  val decode : Type.t -> Types.Type.t t

  (** [exists vars t] binds [vars] as existentially quantified variables. *)
  val exists : variable list -> 'a t -> 'a t

  (** [forall vars f]  binds [vars] as universally quantifier variables. *)
  val forall : variable list -> 'a t -> 'a t

  (** [x #= t] yields the binder that binds [x] to [t].
      It is equivalent to [(x, t)]. *)
  val ( #= ) : Term_var.t -> Type.t -> binding

  (** [def ~bindings ~in_] binds [bindings] in the constraint [in_]. *)
  val def : bindings:binding list -> in_:'a t -> 'a t

  (** [let_ ~rigid ~flexible:n ~bindings ~in_] bindings [rigid]
      variables and [flexible] variables in [bindings]. 
      The bindings are then bound in [in_]. *)
  val let_
    :  rigid: variable list
    -> flexible: variable list
    -> bindings:('a t * binding list)
    -> in_:'b t
    -> (term_binding list * 'a bound * 'b) t

end
