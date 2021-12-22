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

(** This module defines the notion of a "computation".
    
    A computation ['a Computation.t] represents the context for computing
    a value of type ['a] during constrain generation. 

    A computation is defined generically, by the following DSL:
      types         τ ::= τ -> τ | τ computation | τ binder | τ constraint 
                        | ... (standard OCaml types)

      expressions   e ::= x | λ x. e | e e | ... (standard OCaml expressions)
                        | { t } | [ u ]
      
      computation   t ::= let x = t; t | bind x = u; t | return e | ...
      commands
      
      binder        u ::= let x = u; u | sub x = t; u | return e 
      commands          | exists | forall | ...
    
    The above introduces the notion of ['a Binder.t], which encapsulates
    the notion of binding context.
    
    With the applicative syntax for a ['a Constraint.t], we use several "hacks"
    for [Let_syntax] to implement the above DSL using [ppx_let] with some let-operators.  

    TODO: Investigate implementation of a custom PPX. 
*)

module type S = sig
  (** A computation ['a Computation.t] represents a monadic computation
      that produces a value of type ['a]. 
      
      Computations are designed for computating (or generating)
      ['a Constraint.t]'s, thus it's syntax provided by [ppx_let]
      is altered (from standard Monadic Let_syntax) for this. 

      Computations are bound using the [let%bind] syntax:
      {[
        val comp1 : Typedtree.pattern Constraint.t Computation.t

        let%bind pat1 = comp1 in
        let%bind pat2 = comp1 in
        ...
      ]}
  *)
  type 'a t

  include Monad.S with type 'a t := 'a t

  (** [const x] creates a computation that returns a 
      constraint ['a Constraint.t] that evaluates to [x]. *)
  val const : 'a -> 'a Constraint.t t

  (** [fail err] raises the error [err]. *)
  val fail : Sexp.t -> 'a t

  (** [env] returns the environment *)
  val env : Env.t t

  (** [find_label label] returns the corresponding label declaration in 
      the environment w/ label [label]. *)
  val find_label : string -> Types.label_declaration t

  (** [find_constr name] returns the corresponding constructor declaration
      in the environment w/ constructor name [name]. *)
  val find_constr : string -> Types.constructor_declaration t

  (** [substitution] returns the local substitution. *)
  val substitution : Substitution.t t

  val extend_substitution : 'a t -> substitution:Substitution.t -> 'a t

  (** [find_var var] returns the corresponding constraint variable for the
      bound type variable [var] in the local substitution. *)
  val find_var : string -> Constraint.variable t

  (** [of_result result ~message] lifts the result [result] into a computation,
      using [message] to compute the error message for the computation. *)
  val of_result : ('a, 'err) Result.t -> message:('err -> Sexp.t) -> 'a t

  module Binder : sig
    type 'a computation := 'a t

    (** A ['a Binder.t] represents a monadic binding context for a ['b Constraint.t Computation.t]. 

        They are designed to provide an intuitive notion of "compositional" binding 
        (avoiding continuation hell!). 

        Computations are bound using the let-op [let&].
    *)
    type 'a t

    include Monad.S with type 'a t := 'a t

    (* TODO: Formalize this notion of binding context, defined by the methods below.  *)
    val exists : unit -> Constraint.variable t
    val forall : unit -> Constraint.variable t
    val exists_vars : Constraint.variable list -> unit t
    val forall_vars : Constraint.variable list -> unit t
    val exists_bindings : Constraint.Shallow_type.binding list -> unit t
    val of_type : Constraint.Type.t -> Constraint.variable t

    module Let_syntax : sig
      val return : 'a -> 'a t
      val ( let& ) : 'a computation -> ('a -> 'b t) -> 'b t
      val ( >>| ) : 'a Constraint.t -> ('a -> 'b) -> 'b Constraint.t

      val ( <*> )
        :  ('a -> 'b) Constraint.t
        -> 'a Constraint.t
        -> 'b Constraint.t

      module Let_syntax : sig
        val return : 'a -> 'a t
        val map : 'a Constraint.t -> f:('a -> 'b) -> 'b Constraint.t
        val both : 'a Constraint.t -> 'b Constraint.t -> ('a * 'b) Constraint.t
        val bind : 'a t -> f:('a -> 'b t) -> 'b t
      end
    end
  end

  (** [Let_syntax] does not follow the conventional [Let_syntax] signature for 
      a Monad. Instead we have standard [return] and [bind], however, the [map]
      and [both] are used for constructing constraints. 

      This allows the pattern for constructing constraints:
      {[
        let%bind p1 = comp1 in
        let%bind p2 = comp2 in
        return
          (let%map () = var1 =~ var2 in
           ...)
      ]}

      Binders are bound using the let-op [let@]. 
  *)

  module Let_syntax : sig
    val return : 'a -> 'a t
    val ( let@ ) : 'a Binder.t -> ('a -> 'b Constraint.t t) -> 'b Constraint.t t
    val ( >>| ) : 'a Constraint.t -> ('a -> 'b) -> 'b Constraint.t
    val ( <*> ) : ('a -> 'b) Constraint.t -> 'a Constraint.t -> 'b Constraint.t

    module Let_syntax : sig
      val return : 'a -> 'a t
      val map : 'a Constraint.t -> f:('a -> 'b) -> 'b Constraint.t
      val both : 'a Constraint.t -> 'b Constraint.t -> ('a * 'b) Constraint.t
      val bind : 'a t -> f:('a -> 'b t) -> 'b t
    end
  end
end

module type Intf = sig
  module type S = S

  module Expression : sig
    include S

    val run : 'a t -> env:Env.t -> ('a, Sexp.t) Result.t
  end

  module Fragment : sig
    open Constraint

    type t

    val to_bindings : t -> Shallow_type.binding list * binding list
  end

  module Pattern : sig
    include S

    val write : Fragment.t -> unit t
    val extend : string -> Constraint.variable -> unit t
    val run : 'a t -> (Fragment.t * 'a) Expression.t
  end
end
