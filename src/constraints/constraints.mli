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

  (** Constraints require an explicit term algebra for types. 
      
      Which we define by taking the fixpoint of [Type_former.t]
      with constraint variables.      
  *)

  (** [variable] is the for the constraint variables *)
  type variable = private int

  (** [rigid_variable] is the type for rigid constraint type variables. *)
  type rigid_variable = private int

  (** A constraint of type ['a Constraint.t] represents a constraint of
    type ['a]. 
    
    To acquire the a constraint, we first specify it's term variables
    and types using an [Algebra].
  *)

  type 'a t
  and binding = Term_var.t * variable
  and def_binding = binding
  and 'a let_binding
  and 'a let_rec_binding
  and 'a case

  val sexp_of_t : 'a t -> Sexp.t

  (** [fresh ()] creates a fresh constraint variable. *)

  val fresh : unit -> variable
  val fresh_rigid : unit -> rigid_variable

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
      | Rigid_var of rigid_variable
      | Former of t Type_former.t
    [@@deriving sexp_of]

    (** [var 'a] is the representation of the type variable ['a] as the 
        type [t].  *)
    val var : variable -> t

    val rigid_var : rigid_variable -> t

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
    type t =
      | Var
      | Former of variable Type_former.t
    [@@deriving sexp_of]
  end

  module Ambivalent_type : sig
    type t = Shallow_type.t * rigid_variable list [@@deriving sexp_of]

    (** [alias] represents a shallow type binding defined by the grammar:
        alias ::= ɑ :: φ *)
    type alias = variable * t [@@deriving sexp_of]

    type context = alias list

    val of_type : Type.t -> context * variable
  end

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

  (** 
   
  *)

  module Solver : sig
    module Type := Types.Type

    type error =
      [ `Unify of Type.t * Type.t
      | `Cycle of Type.t
      | `Unbound_term_variable of Term_var.t
      | `Unbound_constraint_variable of variable
      | `Rigid_variable_escape
      ]

    val solve : 'a t -> ('a, [> error ]) Result.t
  end

  (** [solve t] solves the constraint [t], returning it's value 
      or an error. *)
  val solve : 'a t -> ('a, [> Solver.error ]) Result.t

  (** [&~] is an infix alias for [both]. *)
  val ( &~ ) : 'a t -> 'b t -> ('a * 'b) t

  (** [t1 >> t2 >> ... >> tn] solves [t1, ..., tn] yielding the value 
      of [tn]. It is the monodial operator of constraints. *)
  val ( >> ) : 'a t -> 'b t -> 'b t

  (** [a =~ a'] is an infix alias for [Eq], denoting the equality
      constraint on type variables. *)
  val ( =~ ) : variable -> variable -> unit t

  val ( =~- ) : variable -> Type.t -> unit t

  (** [as_] is the alias constraint, used for explicit sharing and 
      ambivalence. *)
  val as_ : variable -> Ambivalent_type.t -> unit t

  val ( &= ) : rigid_variable list -> Ambivalent_type.t
  val ( =& ) : variable Type_former.t -> Ambivalent_type.t

  val ( =&= )
    :  variable Type_former.t
    -> rigid_variable list
    -> Ambivalent_type.t

  type 'a bound = Type_var.t list * 'a
  and term_binding = Term_var.t * Types.scheme
  and 'a term_let_binding = term_binding list * 'a bound
  and 'a term_let_rec_binding = term_binding * 'a bound

  (** [inst x a] is the constraint that instantiates [x] to [a].
      It returns the type variable substitution. *)
  val inst : Term_var.t -> variable -> Types.Type.t list t

  (** [decode a] is a constraint that evaluates to the decoded
      type of [a]. *)
  val decode : variable -> Types.Type.t t

  (** [exists bindings t] binds [bindings] existentially in [t]. *)
  val exists : variable list -> 'a t -> 'a t

  (** [forall vars t]  binds [vars] as universally quantifier variables in [t]. *)
  val forall : rigid_variable list -> 'a t -> 'a t

  (** [x #= a] yields the binding that binds [x] to [a].  *)
  val ( #= ) : Term_var.t -> variable -> binding

  (** [def ~bindings ~in_] binds [bindings] in the constraint [in_]. *)
  val def : bindings:def_binding list -> in_:'a t -> 'a t

  (** ([ |., @=>, @~> ]) are combinators designed for the infix construction
      of let and let rec bindings. *)

  val ( @. )
    :  rigid_variable list * Ambivalent_type.context
    -> 'a t
    -> rigid_variable list * Ambivalent_type.context * 'a t

  val ( @=> )
    :  rigid_variable list * Ambivalent_type.context * 'a t
    -> binding list
    -> 'a let_binding

  val ( @~> )
    :  rigid_variable list * Ambivalent_type.context * 'a t
    -> binding
    -> 'a let_rec_binding

  val ( #~> )
    :  rigid_variable list * Ambivalent_type.context * 'a t
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

  module Rigid : sig
    module Type : sig
      type t =
        | Var of rigid_variable
        | Former of t Type_former.t
      [@@deriving sexp_of]
    end

    type t = (Type.t * Type.t) list [@@deriving sexp_of]
  end

  val ( #=> ) : Rigid.t -> 'a t -> 'a t
end

module Private : sig
  module Constraint = Private.Constraint
  include module type of Private.Solver.Private
end