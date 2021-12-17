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

(** The functions of this module are focused on providing an 
    interface for the computations. 
    
    A computation ['a Computation.t] represents the context for computing
    a value of type ['a] during constrain generation. 

    We provide some "hacks" for [ppx_let] to provide a nice EDSL
    for constraint generation.
*)

module type S = sig
  (** A computation ['a Computation.t] represents a computation
      that produces a value of type ['a] (in some constraint 
      generation context).
      
      Computations are bound using the [let%bind] syntax:
      {[
        val comp1 : Typedtree.pattern Constraint.t Computation.t

        let%bind pat1 = comp1 in
        let%bind pat2 = comp1 in
        ...
      ]}

      Computations are designed for computating (or generating)
      ['a Constraint.t]'s, thus it's syntax provided by [ppx_let]
      is altered (from standard Monadic Let_syntax) for this. 
  *)
  type ('a, 'err) t

  include Monad.S2 with type ('a, 'err) t := ('a, 'err) t

  (** [const x] creates a computation that returns a 
      constraint ['a Constraint.t] that evaluates to [x]. *)
  val const : 'a -> ('a Constraint.t, 'err) t

  (** [fail err] raises the error [err]. *)
  val fail : 'err -> ('a, 'err) t

  (** [env] returns the environment *)
  val env : (Env.t, 'err) t

  (** [find_label ~label] returns the corresponding label declaration in 
      the environment w/ label [label]. *)
  val find_label
    :  label:string
    -> (Types.label_declaration, [> `Unbound_label of string ]) t

  (** [find_constr ~name] returns the corresponding constructor declaration
      in the environment w/ constructor name [name]. *)
  val find_constr
    :  name:string
    -> (Types.constructor_declaration, [> `Unbound_constructor of string ]) t

  (** [substitution] returns the local substitution. *)
  val substitution : (Substitution.t, 'err) t

  (** [find_var ~var] returns the corresponding constraint variable for the
      bound type variable [var] in the local substitution. *)
  val find_var
    :  var:string
    -> (Constraint.variable, [> `Unbound_type_variable of string ]) t

  val extend_substitution
    :  ('a, 'err) t
    -> substitution:Substitution.t
    -> ('a, 'err) t

  (** [of_result result] lifts the result [result] into a computation. *)
  val of_result : ('a, 'err) Result.t -> ('a, 'err) t

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
  *)

  module Let_syntax : sig
    val return : 'a -> ('a, 'err) t
    val ( >>| ) : 'a Constraint.t -> ('a -> 'b) -> 'b Constraint.t
    val ( <*> ) : ('a -> 'b) Constraint.t -> 'a Constraint.t -> 'b Constraint.t

    module Let_syntax : sig
      val return : 'a -> ('a, 'err) t
      val map : 'a Constraint.t -> f:('a -> 'b) -> 'b Constraint.t
      val both : 'a Constraint.t -> 'b Constraint.t -> ('a * 'b) Constraint.t
      val bind : ('a, 'err) t -> f:('a -> ('b, 'err) t) -> ('b, 'err) t
    end
  end
end

module type Intf = sig
  module type S = S

  include S

  val run : ('a, 'err) t -> env:Env.t -> ('a, 'err) Result.t

  module Pattern : sig
    type ('a, 'err) e := ('a, 'err) t

    include S

    val write : Fragment.t -> (unit, _) t

    val run
      :  ('a, ([> `Non_linear_pattern of string ] as 'err)) t
      -> (Fragment.t * 'a, 'err) e
  end
end
