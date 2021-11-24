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

module Module_types = Private.Constraint.Module_types

module Make (Algebra : Algebra) : sig
  open Algebra
  module Type_var := Types.Var
  module Type_former := Types.Former

  (** A constraint of type ['a Constraint.t] represents a constraint of
    type ['a]. 
    
    To acquire the a constraint, we first specify it's term variables
    and types. 
    
    The method that one acquires constraints from ['a Computation.t]
    is via the [let%sub] syntax extension. 
    
    {[
      val comp : Typedtree.expression Computation.t

      let%sub cst = comp in
      (* [cst] has the type [Typedtree.expression Constraint.t] *)
    ]} 
  *)

  type 'a t

  and binding

  (** Constraints form a applicative functor, allowing us to combine
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

  (** Constraints require an explicit term algebra for types. 
      
      Which we define by taking the fixpoint of [Type_former.t]
      with constraint variables.      
  *)

  (** [variable] is the for the constraint variables *)
  type variable = private int

  module Type : sig
    type t

    (** [var v] creates a type variable using the constraint variable [v]  *)
    val var : variable -> t

    (** [form f] creates the type former using shallow former
        [f] of type [t Type_former.t]. *)
    val form : t Type_former.t -> t
  end

  type term_binding = Term_var.t * Types.scheme
  type 'a bound = Type_var.t list * 'a

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

  (** [fresh ()] creates a fresh constraint variable. *)
  val fresh : unit -> variable

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

  val solve : 'a t -> 'a
end