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

(* [Module_types] provides the interfaces required "abstract" constraints. *)

module Module_types = Module_types
open Module_types

module Make (Algebra : Algebra) = struct
  open Algebra

  (* Add relevant modules from [Types]. *)

  module Type_var = Types.Var
  module Type_former = Types.Former

  type variable = int

  let fresh =
    let post_incr r =
      let result = !r in
      Int.incr r;
      result
    in
    let next = ref 0 in
    fun () -> post_incr next


  (* The module [Type] provides the concrete representation of types
     (using constraint type variables) in constraints. 

     It is the free monad of the functor [Type_former.t].

     History: This representation was initially used in constraints [t],
     however, the refactor for "Sharing" now uses [Shallow_type.t].
     We however, still use [Type] for a rich interface. 
  *)

  module Type = struct
    (* [t] represents the type defined by the grammar: 
       t ::= ɑ | (t, .., t) F *)
    type t =
      | Var of variable
      | Former of t Type_former.t

    (* [var a] returns the representation of the type variable [a]. *)
    let var a = Var a

    (* [former f] returns the representation of the applied type former [f]. *)
    let former f = Former f
  end

  (* The module [Shallow_type] provides the shallow type definition
     used within constraints. 
     
     This encoding is required for "(Explicit) sharing" of types
     within constraints.

     Types from [Type] are often referred to as "deep" types. 
  *)

  module Shallow_type = struct
    (* [t] represents a shallow type [ρ] is defined by the grammar:
       ρ ::= (ɑ₁, .., ɑ₂) F *)
    type t = variable Type_former.t

    (* [binding] represents a shallow type binding defined by the grammar:
       b ::= ɑ | ɑ :: ρ *)
    type binding = variable * t option

    (* [context] represents a shallow type context Θ. *)
    type context = binding list

    (* [of_type type_] returns the shallow encoding [Θ |> ɑ] of the 
       deep type [type_]. *)
    let of_type type_ =
      let context = ref [] in
      let rec loop t =
        match t with
        | Type.Var var -> var
        | Type.Former former ->
          let var = fresh () in
          let former = Type_former.map former ~f:loop in
          context := (var, Some former) :: !context;
          var
      in
      let var = loop type_ in
      !context, var
  end

  (* ['a t] is a constraint with value type ['a]. *)
  type _ t =
    | True : unit t 
      (** [true] *)
    | Conj : 'a t * 'b t -> ('a * 'b) t 
      (** [C₁ && C₂] *)
    | Eq : variable * variable -> unit t 
      (** [ɑ₁ = ɑ₂] *)
    | Exist : Shallow_type.binding list * 'a t -> 'a t 
      (** [exists Θ. C] *)
    | Forall : variable list * 'a t -> 'a t 
      (** [forall Λ. C] *)
    | Instance : Term_var.t * variable -> Types.Type.t list t 
      (** [x <= ɑ] *)
    | Def : binding list * 'a t -> 'a t
      (** [def x1 : t1 and ... and xn : tn in C] *)
    | Let : 'a let_binding list * 'b t -> ('a term_let_binding list * 'b) t
      (** [let Γ in C] *)
    | Let_rec :
        'a let_rec_binding list * 'b t
        -> ('a term_let_rec_binding list * 'b) t 
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

  (* ['a t] forms an applicative functor, allowing us to combine
     many constraints into a single one using [let%map]:

     {[
       val pat : Typedtree.pattern Constraint.t
       val exp : Typedtree.expression Constraint.t

       let%map pat and exp in
       Texp_fun (pat, ..., exp)
     ]}  
  *)

  include Applicative.Make (struct
    type nonrec 'a t = 'a t

    let return x = Map (True, fun () -> x)
    let map = `Custom (fun t ~f -> Map (t, f))
    let apply t1 t2 = Map (Conj (t1, t2), fun (f, x) -> f x)
  end)

  (* [both] is explicitly defined for efficiency reasons. *)
  let both t1 t2 = Conj (t1, t2)

  module Open_on_rhs_intf = struct
    module type S = sig end
  end

  module Let_syntax = struct
    let return = return

    include Applicative_infix

    module Let_syntax = struct
      let return = return
      let map = map
      let both = both

      module Open_on_rhs = struct end
    end
  end

  (* A continuation of the type [('a, 'b) Continuation.t] is a continuation 
     for constraint computations.
       
     An example usage is binders: e.g. [exists]. However, we also use them
     for typing patterns, etc.
     
     As with standard continuations, they form a monadic structure. 
  *)
  module Continuation = struct
    type nonrec ('a, 'b) t = ('a -> 'b t) -> 'b t

    include Monad.Make2 (struct
      type nonrec ('a, 'b) t = ('a, 'b) t

      let return x k = k x
      let bind t ~f k = t (fun a -> f a k)
      let map = `Define_using_bind
    end)

    let lift t = t
    let run t = t
  end

  (* A binder ['a binder] binds a variable in a constraint
     during it's construction (computation). *)
  type 'a binder = (variable, 'a) Continuation.t

  (* ['n variables] encodes the type of a list containing n variables
     (where n is the type-level natural number representation). *)
  type 'n variables = (variable, 'n) Sized_list.t

  (* [('n, 'a) binders] is a binder that binds ['n] variables,
     known as a "polyvardic binder". *)
  type ('n, 'a) binders = ('n variables, 'a) Continuation.t

  (* [&~] is an infix alias for [both] *)
  let ( &~ ) = both

  (* [t1 >> t2 >> ... >> tn] solves [t1, ..., tn] yielding the value 
     of [tn]. It is the monodial operator of constraints. *)
  let ( >> ) t1 t2 = t1 &~ t2 >>| snd

  (* [a =~ a'] is an infix alias for [Eq], denoting the equality
     constraint on type variables. *)
  let ( =~ ) a1 a2 = Eq (a1, a2)

  (* [inst x a] is the constraint that instantiates [x] to [a].
     It returns the type variable substitution. *)
  let inst x a = Instance (x, a)

  (* [decode a] is a constraint that evaluates to the decoded
     type of [a]. *)
  let decode a = Decode a

  (* [exists bindings t] binds [bindings] existentially in [t]. *)
  let exists bindings t =
    match t with
    | Exist (bindings', t) -> Exist (bindings @ bindings', t)
    | t -> Exist (bindings, t)


  (* [existsn n] binds [n] variables existentially, returning a binder. *)
  let existsn n binder =
    let variables = Sized_list.init n ~f:(fun _ -> fresh ()) in
    exists
      (Sized_list.to_list variables |> List.map ~f:(fun v -> v, None))
      (binder variables)


  let exists1 binder =
    let v = fresh () in
    exists [ v, None ] (binder v)


  (* [of_type type_] constructs the "deep" type [type_], yielding
     the shallow encoding [Θ |> ɑ], then binding the encoding existentially,
     yielding the variable representation [ɑ]. *)
  let of_type type_ =
    Continuation.lift (fun binder ->
        let bindings, var = Shallow_type.of_type type_ in
        exists bindings (binder var))


  (* [forall vars t]  binds [vars] as universally quantifier variables in [t]. *)
  let forall vars t =
    match t with
    | Forall (vars', t) -> Forall (vars @ vars', t)
    | t -> Forall (vars, t)


  (* [foralln n] binds [n] variables universally, returning a continuation. *)
  let foralln n binder =
    let variables = Sized_list.init n ~f:(fun _ -> fresh ()) in
    forall (Sized_list.to_list variables) (binder variables)


  let forall1 binder =
    let v = fresh () in
    forall [ v ] (binder v)


  (* [x #= a] yields the binding that binds [x] to [a]. *)
  let ( #= ) x a : binding = x, a

  (* [def ~bindings ~in_] binds [bindings] in the constraint [in_]. *)
  let def ~bindings ~in_ = Def (bindings, in_)

  (* [rvs, fvs |. in_ @=> bindings] returns the let binding, that binds 
     the rigid vars [rvs] and flexible vars [fvs] w/ the constraint [in_]
     and bindings [bindings]. 
     
     We split this across 2 combinators, using the precedence of [ | > @ ] 
     to ensure that [ |.] binds tighter. Providing a "mixfix" operator. 
  *)
  let ( |. ) (rigid_vars, flexible_vars) in_ = rigid_vars, flexible_vars, in_

  let ( @=> ) (rigid_vars, flexible_vars, in_) bindings =
    Let_binding { rigid_vars; flexible_vars; bindings; in_ }


  (* [let_ ~bindings ~in_] binds the let bindings [bindings] in the constraint [in_]. *)
  let let_ ~bindings ~in_ = Let (bindings, in_)

  (* [rvs, fvs |. in_ @~> binding] returns the let rec binding, that binds 
     the rigid vars [rvs] and flexible vars [fvs] w/ the constraint [in_]
     and binding [binding]. 
  *)
  let ( @~> ) (rigid_vars, flexible_vars, in_) binding =
    Let_rec_binding { rigid_vars; flexible_vars; binding; in_ }


  (* [let_rec ~bindings ~in_] recursively binds the let bindings [bindings] in the 
     constraint [in_]. *)
  let let_rec ~bindings ~in_ = Let_rec (bindings, in_)
end
