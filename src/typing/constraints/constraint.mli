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

  and def_binding = binding

  and 'a let_binding

  and 'a let_rec_binding

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

  module Solver : sig
    module Type := Types.Type

    type error =
      [ `Unify of Type.t * Type.t
      | `Cycle of Type.t
      | `Unbound_term_variable of Term_var.t
      | `Unbound_constraint_variable of variable
      | `Rigid_variable_escape of Type_var.t
      ]

    val solve : 'a t -> ('a, error) Result.t
  end

  (** [solve t] solves the constraint [t], returning it's value 
      or an error. *)
  val solve : 'a t -> ('a, Solver.error) Result.t

  (** The module [Type] provides the concrete representation of types
      (using constraint type variables) in constraints. 

      It is the free monad of the functor [Type_former.t].

      History: This representation was initially used in constraints [t],
      however, the refactor for "Sharing" now uses [Shallow_type.t].
      We however, still use [Type] for a rich interface. 
  *)

  module Type : sig
    (** [t] represents the type defined by the grammar: 
        t ::= ɑ | (t, .., t) F *)
    type t =
      | Var of variable
      | Former of t Type_former.t

    (** [var 'a] is the representation of the type variable ['a] as the 
        type [t].  *)
    val var : variable -> t

    (** [former f] is the representation of the concrete type former [f] in
        type [t]. *)
    val former : t Type_former.t -> t
  end

  (** The module [Shallow_type] provides the shallow type definition
      used within constraints. 
      
      This encoding is required for "(Explicit) sharing" of types
      within constraints.

      Types from [Type] are often referred to as "deep" types. 
  *)

  module Shallow_type : sig
    (** [t] represents a shallow type [ρ] is defined by the grammar:
        ρ ::= (ɑ₁, .., ɑ₂) F *)
    type t = variable Type_former.t

    (** [binding] represents a shallow type binding defined by the grammar:
        b ::= ɑ | ɑ :: ρ *)
    type binding = variable * t option

    (** [context] represents a shallow type context Θ. *)
    type context = binding list

    (** [of_type type_] returns the shallow encoding [Θ |> ɑ] of the deep 
        type [type_]. *)
    val of_type : Type.t -> context * variable
  end

  type 'a bound = Type_var.t list * 'a

  and term_binding = Term_var.t * Types.scheme

  and 'a term_let_binding = term_binding list * 'a bound

  and 'a term_let_rec_binding = term_binding * 'a bound

  (** A continuation of the type [('a, 'b) Continuation.t] is a continuation 
      for constraint computations.
        
      An example usage is binders: e.g. [exists]. However, we also use them
      for typing patterns, etc.
      
      As with standard continuations, they form a monadic structure. 
  *)
  module Continuation : sig
    include
      Monad.Monad_trans.S2
        with type ('a, 'b) t = ('a -> 'b t) -> 'b t
         and type ('a, 'b) m := ('a -> 'b t) -> 'b t
         and type ('a, 'b) e := ('a -> 'b t) -> 'b t

    include Monad.S2 with type ('a, 'b) t := ('a, 'b) t
  end

  (** ['n variables] encodes the type of a list containing n variables
      (where n is the type-level natural number representation). *)
  type 'n variables = (variable, 'n) Sized_list.t

  (** A binder ['a binder] binds a variable in a constraint
      during it's construction (computation). *)
  type 'a binder = (variable, 'a) Continuation.t

  (** [('n, 'a) binders] is a binder that binds ['n] variables,
      known as a "polyvardic binder". *)
  type ('n, 'a) binders = ('n variables, 'a) Continuation.t

  (** [&~] is an infix alias for [both]. *)
  val ( &~ ) : 'a t -> 'b t -> ('a * 'b) t

  (** [t1 >> t2 >> ... >> tn] solves [t1, ..., tn] yielding the value 
      of [tn]. It is the monodial operator of constraints. *)
  val ( >> ) : 'a t -> 'b t -> 'b t

  (** [a =~ a'] is an infix alias for [Eq], denoting the equality
      constraint on type variables. *)
  val ( =~ ) : variable -> variable -> unit t

  (** [inst x a] is the constraint that instantiates [x] to [a].
      It returns the type variable substitution. *)
  val inst : Term_var.t -> variable -> Types.Type.t list t

  (** [decode a] is a constraint that evaluates to the decoded
      type of [a]. *)
  val decode : variable -> Types.Type.t t

  (** [exists bindings t] binds [bindings] existentially in [t]. *)
  val exists : Shallow_type.binding list -> 'a t -> 'a t

  (** [existsn n] binds [n] variables existentially, returning a binder. *)
  val existsn : 'n Size.t -> ('n, 'a) binders

  val exists1 : 'a binder

  (** [of_type type_] constructs the "deep" type [type_], yielding
      the shallow encoding [Θ |> ɑ], then binding the encoding existentially,
      yielding the variable representation [ɑ]. *)
  val of_type : Type.t -> 'a binder

  (** [forall vars t]  binds [vars] as universally quantifier variables in [t]. *)
  val forall : variable list -> 'a t -> 'a t

  (** [foralln n] binds [n] variables universally, returning a binder. *)
  val foralln : 'n Size.t -> ('n, 'a) binders

  val forall1 : 'a binder

  (** [x #= a] yields the binding that binds [x] to [a].  *)
  val ( #= ) : Term_var.t -> variable -> binding

  (** [def ~bindings ~in_] binds [bindings] in the constraint [in_]. *)
  val def : bindings:def_binding list -> in_:'a t -> 'a t

  (** ([ |., @=>, @~> ]) are combinators designed for the infix construction
      of let and let rec bindings. *)

  val ( |. )
    :  variable list * Shallow_type.binding list
    -> 'a t
    -> variable list * Shallow_type.binding list * 'a t

  val ( @=> )
    :  variable list * Shallow_type.binding list * 'a t
    -> binding list
    -> 'a let_binding

  val ( @~> )
    :  variable list * Shallow_type.binding list * 'a t
    -> binding
    -> 'a let_rec_binding

  (** [let_ ~bindings ~in_] binds the let bindings [bindings] in the constraint [in_]. *)
  val let_
    :  bindings:'a let_binding list
    -> in_:'b t
    -> ('a term_let_binding list * 'b) t

  (** [let_rec ~bindings ~in_] recursively binds the let bindings [bindings] in the 
      constraint [in_]. *)
  val let_rec
    :  bindings:'a let_rec_binding list
    -> in_:'b t
    -> ('a term_let_rec_binding list * 'b) t
end