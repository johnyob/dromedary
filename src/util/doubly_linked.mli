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

module Elt : sig
  type 'a t [@@deriving sexp_of]

  val get_value : 'a t -> 'a
  val set_value : 'a t -> 'a -> unit

  val make : 'a -> 'a t
end

type 'a t [@@deriving sexp_of]

val first : 'a t -> 'a Elt.t option

val empty : unit -> 'a t

val remove : 'a t -> 'a Elt.t -> unit

val remove_first : 'a t -> 'a option

val insert_first : 'a t -> 'a Elt.t -> unit

val insert_first_elt : 'a t -> 'a -> 'a Elt.t

val merge : 'a t -> 'a t -> compare:('a -> 'a -> int) -> 'a t

val map : 'a t -> f:('a -> 'b) -> 'b t

(** Must not modify the structure while iterating *)
val unsafe_iter : 'a t -> f:('a Elt.t -> unit) -> unit

val iter : 'a t -> f:('a -> unit) -> unit

val fold : 'a t -> init:'b -> f:('a -> 'b -> 'b) -> 'b


