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
module Module_types = Module_types

module Make (Algebra : Algebra) : sig
  open Algebra
  module Label := Types.Label
  module Type_var := Types.Var
  module Type_former := Types.Former

  module Decoded :
    Decoded
      with type label := Label.t
       and type 'a former := 'a Type_former.t

  (** Constraints require an explicit term algebra for types. 
      
      Which we define by taking the fixpoint of [Type_former.t]
      with constraint variables.      
  *)

  (** [variable] is the for the constraint variables *)
  type variable = private int

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

  val sexp_of_t : 'a t -> Sexp.t

  (** [fresh ()] creates a fresh constraint variable. *)

  val fresh : unit -> variable

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
      | Row_cons of Label.t * t * t
      | Row_uniform of t
      | Mu of variable * t
      | Let of variable * t * t
    [@@deriving sexp_of]

    (** [var 'a] is the representation of the type variable ['a] as the 
        type [t].  *)
    val var : variable -> t

    (** [former f] is the representation of the concrete type former [f] in
        type [t]. *)
    val former : t Type_former.t -> t

    (** [mu 'a t] is the representation of the recursive type [mu 'a. t] *)
    val mu : variable -> t -> t

    val let_ : binding:variable * t -> in_:t -> t
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
    type t =
      | Former of variable Type_former.t
      | Row_cons of Label.t * variable * variable
      | Row_uniform of variable
      | Mu of variable
      | Let of variable
    [@@deriving sexp_of]

    (** [binding] represents a shallow type binding defined by the grammar:
        b ::= ɑ :: ρ *)
    type binding = variable * t [@@deriving sexp_of]

    module Ctx : sig
      type t = variable list * binding list [@@deriving sexp_of]

      val merge : t -> t -> t
    end

    (** [encoded_type] represents the shallow encoding [Θ |> ɑ]
            of a deep type. *)
    type encoded_type = Ctx.t * variable [@@deriving sexp_of]

    (** [of_type type_] returns the shallow encoding [Θ |> ɑ] of the deep 
            type [type_]. *)
    val of_type : Type.t -> encoded_type
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

  module Abbrev_type : sig
    type t [@@deriving sexp_of, compare]

    val make_var : unit -> t
    val make_former : t Type_former.t -> t
  end

  module Abbreviations : sig
    type t

    val empty : t
    val add : t -> abbrev:Abbrev_type.t Type_former.t * Abbrev_type.t -> t
  end

  module Solver : sig
    type error =
      [ `Unify of Decoded.Type.t * Decoded.Type.t
      | `Cycle of Decoded.Type.t
      | `Unbound_term_variable of Term_var.t
      | `Unbound_constraint_variable of variable
      | `Rigid_variable_escape of Type_var.t
      | `Cannot_flexize of Type_var.t
      | `Scope_escape of Decoded.Type.t
      | `Non_rigid_equations
      | `Inconsistent_equations
      ]
  end

  (** [solve t] solves the constraint [t], returning it's value 
      or an error. *)
  val solve
    :  ?debug:bool
    -> abbrevs:Abbreviations.t
    -> 'a t
    -> ('a, [> Solver.error ]) Result.t

  type existential_context = Shallow_type.Ctx.t [@@deriving sexp_of]
  type universal_context = variable list [@@deriving sexp_of]
  type equations = (Type.t * Type.t) list [@@deriving sexp_of]

  (** [&~] is an infix alias for [both]. *)
  val ( &~ ) : 'a t -> 'b t -> ('a * 'b) t

  (** [t1 >> t2 >> ... >> tn] solves [t1, ..., tn] yielding the value 
      of [tn]. It is the monodial operator of constraints. *)
  val ( >> ) : 'a t -> 'b t -> 'b t

  (** [a =~ a'] is an infix alias for [Eq], denoting the equality
      constraint on type variables. *)
  val ( =~ ) : variable -> variable -> unit t

  val ( =~= ) : variable -> Shallow_type.t -> unit t
  val ( =~- ) : variable -> Type.t -> unit t

  type 'a bound = Decoded.Var.t list * 'a
  and term_binding = Term_var.t * Decoded.scheme
  and 'a term_let_binding = term_binding list * 'a bound
  and 'a term_let_rec_binding = term_binding * 'a bound

  (** [inst x a] is the constraint that instantiates [x] to [a].
      It returns the type variable substitution. *)
  val inst : Term_var.t -> variable -> Decoded.Type.t list t

  (** [decode a] is a constraint that evaluates to the decoded
      type of [a]. *)
  val decode : variable -> Decoded.Type.t t

  (** [exists ~ctx t] binds existential context [ctx] in [t]. *)
  val exists : ctx:existential_context -> 'a t -> 'a t

  (** [forall ~ctx t] binds universal context [ctx] in [t]. *)
  val forall : ctx:universal_context -> 'a t -> 'a t

  (** [x #= a] yields the binding that binds [x] to [a].  *)
  val ( #= ) : Term_var.t -> variable -> binding

  (** [def ~bindings ~in_] binds [bindings] in the constraint [in_]. *)
  val def : bindings:def_binding list -> in_:'a t -> 'a t

  (** [equations #=> t] is an alias for the implication constraint [Implication (equations, t)]. *)
  val ( #=> ) : equations -> 'a t -> 'a t

  (** [let_ ~binding ~in_] binds the let binding [binding] in the constraint [in_]. *)
  val let_
    :  bindings:'a let_binding list
    -> in_:'b t
    -> ('a term_let_binding list * 'b) t

  val let_0 : in_:'a t -> 'a bound t
  val let_1 : binding:'a let_binding -> in_:'b t -> ('a term_let_binding * 'b) t

  (** [let_rec ~bindings ~in_] recursively binds the let bindings [bindings] in the 
      constraint [in_]. *)
  val let_rec
    :  bindings:'a let_rec_binding list
    -> in_:'b t
    -> ('a term_let_rec_binding list * 'b) t

  module Binding : sig
    type ctx = universal_context * existential_context [@@deriving sexp_of]

    val let_
      :  ctx:ctx
      -> is_non_expansive:bool
      -> bindings:binding list
      -> in_:'a t
      -> equations:equations
      -> 'a let_binding

    val let_mrec : ctx:ctx -> binding:binding -> in_:'a t -> 'a let_rec_binding

    val let_prec
      :  universal_ctx:universal_context
      -> annotation:Shallow_type.encoded_type
      -> term_var:Term_var.t
      -> in_:'a t
      -> 'a let_rec_binding
  end

  (** Constraints may be used to define "structures" of constraints. 

      Intuitively these correspond to structures in the expression language. 
      
      These structures also form applicatives functors :) 
  *)

  module Structure : sig
    module Item : sig
      type nonrec 'a let_rec_binding = 'a let_rec_binding
      and 'a let_binding

      module Binding : sig
        type ctx = universal_context * existential_context [@@deriving sexp_of]

        val let_
          :  ctx:ctx
          -> is_non_expansive:bool
          -> bindings:binding list
          -> in_:'a t
          -> 'a let_binding

        val let_mrec
          :  ctx:ctx
          -> binding:binding
          -> in_:'a t
          -> 'a let_rec_binding

        val let_prec
          :  universal_ctx:universal_context
          -> annotation:Shallow_type.encoded_type
          -> term_var:Term_var.t
          -> in_:'a t
          -> 'a let_rec_binding
      end

      type 'a t

      val sexp_of_t : _ t -> Sexp.t

      include Applicative.S with type 'a t := 'a t
      include Applicative.Let_syntax with type 'a t := 'a t

      val let_ : bindings:'a let_binding list -> 'a term_let_binding list t
      val let_1 : binding:'a let_binding -> 'a term_let_binding t

      val let_rec
        :  bindings:'a let_rec_binding list
        -> 'a term_let_rec_binding list t

      val def : bindings:def_binding list -> unit t
    end

    type 'a t = 'a Item.t list

    val sexp_of_t : _ t -> Sexp.t

    val solve
      :  ?debug:bool
      -> abbrevs:Abbreviations.t
      -> 'a t
      -> ('a list, [> Solver.error ]) Result.t
  end
end

module Private : sig
  module Constraint = Constraint
  include module type of Solver.Private
end