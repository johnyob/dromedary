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

open Base
open Misc

(* ------------------------------------------------------------------------- *)

(** [Intf] provides the interfaces required for constraints. *)

module Intf = Intf

(* ------------------------------------------------------------------------- *)

open Intf

(** The [Make] functor defines the constraint syntax, parameterized
    by term variables [Term_var] and decoded types [Types].  *)

module Make (Term_var : Term_var) (Types : Types) : sig
  (* Useful aliases *)

  module Type_var := Types.Var
  module Type_former := Types.Former

  (* ----------------------------------------------------------------------- *)

  (** [variable] is the type for constraint "type" variables. *)

  type variable = private int

  (** [fresh ()] creates a fresh constraint variable. *)

  val fresh : unit -> variable

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
      | Form of t Type_former.t

    (** [var 'a] is the representation of the type variable ['a] as the 
        type [t]. See [Var] above. *)
    val var : variable -> t

    (** [form f] is the representation of the concrete type former [f] in
        type [t]. See [Form] above. *)
    val form : t Type_former.t -> t
  end

  (* ----------------------------------------------------------------------- *)

  (** ['a t] is a constraint with value type ['a]. 
          
      In the meta-theory, the constraint language has a defined type
      system. 
      
      In our implementation, we use GADTs to implement the 
      type system, where the type parameter ['a] denotes the type of 
      the constraint. *)

  type _ t =
    | Cst_true : unit t 
    (** [true] *)
    | Cst_conj : 'a t * 'b t -> ('a * 'b) t 
    (** [C1 && C2] *)
    | Cst_eq : Type.t * Type.t -> unit t 
    (** [t1 = t2] *)
    | Cst_exist : variable list * 'a t -> 'a t 
    (** [exists a. C] *)
    | Cst_forall : variable list * 'a t -> 'a t 
    (** [forall a. C] *)
    | Cst_instance : Term_var.t * Type.t -> Types.Type.t list t 
    (** [x <= t] *)
    | Cst_def : def_binding list * 'a t -> 'a t
    (** [def x1 : t1 and ... and xn : tn in C] *)
    | Cst_let : 'a let_binding * 'b t -> (term_binding list * 'a bound * 'b) t
    (** [let a1 ... am [C]. (x1 : t1 and ... xk : tk) in C']. *)
    | Cst_map : 'a t * ('a -> 'b) -> 'b t 
    (** [map C f]. *)
    | Cst_match : 'a t * 'b case list -> ('a * 'b list) t
    (** [match C with (... | (x1 : t1 ... xn : tn) -> Ci | ...)]. *)
    | Cst_decode : Type.t -> Types.Type.t t (** [decode t] *)

  and term_binding = Term_var.t * Types.scheme

  and binding = Term_var.t * Type.t

  and def_binding = binding

  and 'a scheme =
    { csch_rigid_vars : variable list
    ; csch_flexible_vars : variable list
    ; csch_cst : 'a t
    }

  and 'a let_binding =
    { clb_sch : 'a scheme
    ; clb_bs : binding list
    }

  and 'a bound = Type_var.t list * 'a

  and 'a case =
    { ccase_bs : binding list
    ; ccase_cst : 'a t
    }

  (* ----------------------------------------------------------------------- *)

  (* ['a t] forms an applicative functor *)

  include Applicative.S with type 'a t := 'a t
  include Applicative.Let_syntax with type 'a t := 'a t

  (* ----------------------------------------------------------------------- *)

  (* Combinators *)

  val ( &~ ) : 'a t -> 'b t -> ('a * 'b) t
  val ( >> ) : 'a t -> 'b t -> 'b t
  val ( =~ ) : Type.t -> Type.t -> unit t
  val inst : Term_var.t -> Type.t -> Types.Type.t list t
  val decode : Type.t -> Types.Type.t t

  (* ----------------------------------------------------------------------- *)

  (* Continuations, binders and quantifiers *)

  module Continuation : sig
    (** A continuation of the type [('a, 'b) t] is a continuation for
        constraint computations.

        An example usage is binders: e.g. [exists]. However, we also use them
        for typing patterns, etc.

        As with standard continuations, they form a monadic structure. *)
    type ('a, 'b) t

    include Monad.S2 with type ('a, 'b) t := ('a, 'b) t

    (* TODO: Make into transformer! *)

  end

  (* [('n, 'a) binder] is a binder that binds ['n] variables. *)

  type ('n, 'a) binder = ('n variables, 'a) Continuation.t

  (* ['n variables] encodes the type of a list containing n variables
         (where n is the type-level natural number representation). *)
  and 'n variables = (variable, 'n) Sized_list.t

  (* [('m, 'n, 'a) binder2] is the 2 kinded version of [binder], bindings ['m]
         and ['n] rigid and flexible variables, respectively. *)
  type ('m, 'n, 'a) binder2 = ('m variables * 'n variables, 'a) Continuation.t

  (* [exists n f] binds [n] existentially quantified variables, *)
  val exists : 'n Size.t -> ('n, 'a) binder
  val forall : 'n Size.t -> ('n, 'a) binder

  (* ----------------------------------------------------------------------- *)

  val ( #= ) : Term_var.t -> Type.t -> binding
  val def : def_binding list -> 'a t -> 'a t

  val scheme
    :  rigid:variable list
    -> flexible:variable list
    -> 'a t
    -> 'a scheme

  val let_
    :  'm Size.t
    -> 'n Size.t
    -> ('m variables * 'n variables -> 'a t)
    -> ('m variables * 'n variables -> def_binding list)
    -> 'b t
    -> (term_binding list * 'a bound * 'b) t
end
