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
    interface between constraints ['a Constraint.t] and "computations" 
    ['a Computation.t]. 

    A computation ['a Computation.t] represents a method for computing 
    a constraint of type ['a]. 

    Since ['a Constraint.t] doesn't form a monad, we require an 
    abstract that is "stronger" than a applicative, but weaker than 
    a monad. 
    
    We have selected "Arrow" as our primary abstraction, basing
    our work on Yallop et al's Arrow Calculus (with an API inspired
    by Bonsai, exploiting the new and shiny features of [ppx_let]). 
*)

module type Basic = Monad.S
module type Basic2 = Monad.S2

module type S = sig
  (** A computation ['a Computation.t] represents a computation
      that produces an ['a Constraint.t]. 
      
      Computations share many of the semantics of OCaml functions, 
      namely functions that return values of type ['a Constraint.t].
      (If in doubt, think what a function would do).

      Computations are bound using the [let%sub] syntax:
      
      {[
        val comp1 : Typedtree.pattern Computation.t

        let%sub pat1 = comp1 in
        let%sub pat2 = comp1 in
        ...
      ]}

      evaluates the computation [comp1] *twice*. Note that [pat1]
      and [pat2] could (and are likely to) have different values
      (due to side-effecting state). 
  *)

  type 'a t

  (** Similarly to ['a Constraint.t], computations ['a Computation.t] 
      form an applicative functor.

      Note that ['a Computation.t] are often built from Monads. 
      This reduction in "power" is due to the composition of 
      Monads and Applicatives. 
  *)

  include Applicative.S with type 'a t := 'a t
  include Applicative.Let_syntax with type 'a t := 'a t
end

module type S2 = sig
  type ('a, 'b) t

  include Applicative.S2 with type ('a, 'b) t := ('a, 'b) t
  include Applicative.Let_syntax2 with type ('a, 'b) t := ('a, 'b) t
end

module type Intf = sig
  module type Basic = Basic
  module type Basic2 = Basic2
  module type S = S
  module type S2 = S2

  module Make (Algebra : Algebra) (Basic : Basic) : sig
    module Constraint := Constraint.Make(Algebra)
    module Computation : S

    val lift : 'a Constraint.t Basic.t -> 'a Computation.t
    val run : 'a Computation.t -> 'a Constraint.t Basic.t

    (** [constraint_ cst] creates a computation ['a Computation.t] 
        that returns the constraint [cst]. *)
    val constraint_ : 'a Constraint.t -> 'a Computation.t

    (** [const x] creates a computation ['a Computation.t] that returns a 
      constraint ['a Constraint.t] that evaluates to [x]. *)
    val const : 'a -> 'a Computation.t

    (** [pure ~f] lifts a regular OCaml function [f] into a "computation"
        function, taking a ['a Constraint.t] as input, producing a 
        ['a Computation.t] as output. 
        
        In [Let_syntax] this is known as [arr]. *)
    val pure : 'a Constraint.t -> f:('a -> 'b) -> 'b Computation.t

    (** This is a handcrafted [Let_syntax] module, designed for [let%sub]
        + ease of use.  *)

    module Let_syntax : sig
      val return : 'a Constraint.t -> 'a Computation.t
      val ( >>| ) : 'a Constraint.t -> ('a -> 'b) -> 'b Constraint.t

      val ( <*> )
        :  ('a -> 'b) Constraint.t
        -> 'a Constraint.t
        -> 'b Constraint.t

      module Let_syntax : sig
        val return : 'a Constraint.t -> 'a Computation.t
        val map : 'a Constraint.t -> f:('a -> 'b) -> 'b Constraint.t
        val both : 'a Constraint.t -> 'b Constraint.t -> ('a * 'b) Constraint.t
        val bind : 'a Basic.t -> f:('a -> 'b Computation.t) -> 'b Computation.t

        val sub
          :  ?here:Source_code_position.t
          -> 'a Computation.t
          -> f:('a Constraint.t -> 'b Computation.t)
          -> 'b Computation.t

        val arr
          :  ?here:Source_code_position.t
          -> 'a Constraint.t
          -> f:('a -> 'b)
          -> 'b Computation.t
      end
    end
  end

  module Make2 (Algebra : Algebra) (Basic : Basic2) : sig
    module Constraint := Constraint.Make(Algebra)
    module Computation : S2

    val lift : ('a Constraint.t, 'b) Basic.t -> ('a, 'b) Computation.t
    val run : ('a, 'b) Computation.t -> ('a Constraint.t, 'b) Basic.t
    val constraint_ : 'a Constraint.t -> ('a, 'b) Computation.t
    val const : 'a -> ('a, 'b) Computation.t
    val pure : 'a Constraint.t -> f:('a -> 'b) -> ('b, 'c) Computation.t

    module Let_syntax : sig
      val return : 'a Constraint.t -> ('a, 'b) Computation.t
      val ( >>| ) : 'a Constraint.t -> ('a -> 'b) -> 'b Constraint.t

      val ( <*> )
        :  ('a -> 'b) Constraint.t
        -> 'a Constraint.t
        -> 'b Constraint.t

      module Let_syntax : sig
        val return : 'a Constraint.t -> ('a, 'b) Computation.t
        val map : 'a Constraint.t -> f:('a -> 'b) -> 'b Constraint.t
        val both : 'a Constraint.t -> 'b Constraint.t -> ('a * 'b) Constraint.t

        val bind
          :  ('a, 'c) Basic.t
          -> f:('a -> ('b, 'c) Computation.t)
          -> ('b, 'c) Computation.t

        val sub
          :  ?here:Source_code_position.t
          -> ('a, 'c) Computation.t
          -> f:('a Constraint.t -> ('b, 'c) Computation.t)
          -> ('b, 'c) Computation.t

        val arr
          :  ?here:Source_code_position.t
          -> 'a Constraint.t
          -> f:('a -> 'b)
          -> ('b, 'c) Computation.t
      end
    end
  end
end