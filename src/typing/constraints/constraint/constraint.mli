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

  (** While "deep" types (the above) are often used within the interface,
      "shallow" types are used within the constraint representation for
      explicit sharing of types. *)

  module Shallow_type : sig
    (** A shallow type [ρ] is defined by the grammar:
        ρ ::= (ɑ₁, .., ɑ₂) F *)
    type t = variable Type_former.t

    (** A shallow type binding is defined by the grammar:
          binding ::= ɑ | ɑ = ρ *)
    type binding = variable * t option
    
    (** A shallow type context Δ is a list of shallow
        type bindings. *)
    type context = binding list

    val of_type : Type.t -> context * variable
  end

  (** ['a t] is a constraint with value type ['a]. 
          
      In the meta-theory, the constraint language has a defined type
      system. 
      
      In our implementation, we use GADTs to implement the 
      type system, where the type parameter ['a] denotes the type of 
      the constraint. 
  *)

  type _ t =
    | True : unit t 
      (** [true] *)
    | Conj : 'a t * 'b t -> ('a * 'b) t 
      (** [C₁ && C₂] *)
    | Eq : variable * variable -> unit t 
      (** [ɑ₁ = ɑ₂] *)
    | Exist : Shallow_type.binding list * 'a t -> 'a t 
      (** [exists Δ. C] *)
    | Forall : variable list * 'a t -> 'a t 
      (** [forall Θ. C] *)
    | Instance : Term_var.t * variable -> Types.Type.t list t 
      (** [x <= ɑ] *)
    | Def : binding list * 'a t -> 'a t
      (** [def x1 : t1 and ... and xn : tn in C] *)
    | Let : 'a let_binding * 'b t -> ('a term_let_binding * 'b) t
      (** [let ∀ Θ ∃ Δ. C => (x₁ : Ɣ₁ and ... xₘ : Ɣₘ) in C']. *)
    | Letn : 'a let_binding list * 'b t -> ('a term_let_binding list * 'b) t
      (** [let Γ in C] *)
    | Let_rec : 'a let_rec_binding list * 'b t -> ('a term_let_rec_binding list * 'b) t
      (** [let rec Γ in C] *)
    | Map : 'a t * ('a -> 'b) -> 'b t 
      (** [map C f]. *)
    | Match : 'a t * 'b case list -> ('a * 'b list) t
      (** [match C with (... | (x₁ : ɑ₁ ... xₙ : ɑₙ) -> Cᵢ | ...)]. *)
    | Decode : variable -> Types.Type.t t 
      (** [decode ɑ] *)

  and binding = Term_var.t * variable

  and def_binding = binding 

  and 'a let_binding =
    | Let_binding of
        { rigid_vars : variable list
        ; flexible_vars : Shallow_type.binding list
        ; bindings : binding list
        ; in_ : 'a t
        }

  and 'a let_rec_binding = 
    | Let_rec_binding of
      { rigid_vars : variable list
      ; flexible_vars : Shallow_type.binding list
      ; binding : binding
      ; in_ : 'a t
      }
    
  and 'a case =
    | Case of
        { bindings : binding list
        ; in_ : 'a t
        }
    
  and 'a bound = Type_var.t list * 'a

  and term_binding = Term_var.t * Types.scheme

  and 'a term_let_binding = term_binding list * 'a bound

  and 'a term_let_rec_binding = term_binding * 'a bound


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

  module Continuation : sig
    include Monad.Monad_trans.S2 
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
  type ('n, 'a) bindern = ('n variables, 'a) Continuation.t

  (** [&~] is an infix alias for [both]. *)
  val ( &~ ) : 'a t -> 'b t -> ('a * 'b) t

  (** [c1 >> c2 >> ... >> cn] solves [c1, ..., cn] yielding the value 
      of [cn]. It is the monodial operator of constraints. *)
  val ( >> ) : 'a t -> 'b t -> 'b t

  (** [t =~ t'] is an infix alias for [Cst_eq], denoting the equality
      constraint on types. *)
  val ( =~ ) : variable -> variable -> unit t

  (** [inst x t] is the constraint that instantiates [x] to [t].
      It returns the type variable substitution. *)
  val inst : Term_var.t -> variable -> Types.Type.t list t

  (** [decode t] is a constraint that evaluates to the decoded
      type of [t]. *)
  val decode : variable -> Types.Type.t t

  (** [exists vars t] binds [vars] as existentially quantified variables. *)
  val exists : Shallow_type.binding list -> 'a t -> 'a t
  
  val exists1 : 'a binder
  val existsn : 'n Size.t -> ('n, 'a) bindern
  
  (** [of_type type_] constructs the type [type_] and then binds 
      to an existentially quantified variable. *)
  val of_type : Type.t -> 'a binder
  
  (** [forall vars f]  binds [vars] as universally quantifier variables. *)
  val forall : variable list -> 'a t -> 'a t
  
  val forall1 : 'a binder
  val foralln : 'n Size.t -> ('n, 'a) bindern

  (** [x #= t] yields the binder that binds [x] to [t].
      It is equivalent to [(x, t)]. *)
  val ( #= ) : Term_var.t -> variable -> binding

  (** [def ~bindings ~in_] binds [bindings] in the constraint [in_]. *)
  val def : bindings:binding list -> in_:'a t -> 'a t

  (** [let_ ~rigid ~flexible:n ~bindings ~in_] bindings [rigid]
      variables and [flexible] variables in [bindings]. 
      The bindings are then bound in [in_]. *)
  val let_
    :  rigid: variable list
    -> flexible: Shallow_type.binding list
    -> bindings:('a t * binding list)
    -> in_:'b t
    -> ('a term_let_binding * 'b) t

end
