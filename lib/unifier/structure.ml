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

(* This module implements signature used for unification structures. *)

open Base

module type S = sig
  (** A structure defines the internal structure of terms in the unification 
      problem. *)
  type 'a t [@@deriving sexp_of]

  (** ['a ctx] represents the arbitrary context used by [merge] *)
  type 'a ctx

  (** [Cannot_merge] is raised by [merge] iff the 2 structures are not "consistent". *)
  exception Cannot_merge

  (** [merge ~ctx ~create ~unify t1 t2] determines computes the merged
      structure of [t1] and [t2]. If the structures are inconsistent, then
      {!Cannot_merge} is raised. 

      [merge] can emit first-order equalities using [unify], or create new 
      terms from structures using [create]. 

      An additional context [ctx] is provided since consistency might
      be contextual.  
  *)
  val merge
    :  ctx:'a ctx
    -> create:('a t -> 'a)
    -> unify:('a -> 'a -> unit)
    -> 'a t
    -> 'a t
    -> 'a t

  (** [map t ~f] traverses [t], applying the transformation [f]. *)
  val map : 'a t -> f:('a -> 'b) -> 'b t

  (** [iter t ~f] traverses [t], executing [f] on each child. *)
  val iter : 'a t -> f:('a -> unit) -> unit

  (** [fold t ~f ~init] performs the computation of [f], traversing
      over [t] with the initial accumulator value of [init]. *)
  val fold : 'a t -> f:('a -> 'b -> 'b) -> init:'b -> 'b
end

