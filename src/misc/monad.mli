(* ***************************************************************************
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

open Base

module type Monoid = sig
  type t

  val zero : t
  val plus : t -> t -> t
end

module Monad_trans : sig
  module type S2 = sig
    type ('a, 'b) t
    type ('a, 'b) m
    type ('a, 'b) e

    val lift : ('a, 'b) m -> ('a, 'b) t
    val run : ('a, 'b) t -> ('a, 'b) e
  end
end

module Writer_monad : sig
  module type S2 = sig
    include Monad_trans.S2

    type state

    val write : state -> (unit, 'b) t
    val read : ('a, 'b) t -> (state, 'b) t
    val listen : ('a, 'b) t -> (state * 'a, 'b) t

    include Monad.S2 with type ('a, 'b) t := ('a, 'b) t
  end

  type ('state, 'a) writer

  module Make2 (S : Monoid) (M : Monad.S2) :
    S2
      with type state := S.t
       and type ('a, 'b) m := ('a, 'b) M.t
       and type ('a, 'b) e := (S.t * 'a, 'b) M.t
end

module Reader_monad : sig
  module type S2 = sig
    include Monad_trans.S2

    type state

    val read : unit -> (state, 'a) t
    val local : ('a, 'b) t -> f:(state -> state) -> ('a, 'b) t

    include Monad.S2 with type ('a, 'b) t := ('a, 'b) t
  end

  type ('state, 'a) reader

  module Make2 (T : T) (M : Monad.S2) :
    S2
      with type state := T.t
       and type ('a, 'b) m := ('a, 'b) M.t
       and type ('a, 'b) e := T.t -> ('a, 'b) M.t
end

module Indexed_continuation : sig
  type ('a, 'i, 'j) t

  include Monad.S_indexed with type ('a, 'i, 'j) t := ('a, 'i, 'j) t

  val lift : (('a -> 'j) -> 'i) -> ('a, 'i, 'j) t
  val run : ('a, 'i, 'j) t -> ('a -> 'j) -> 'i
end

module Continuation : sig
  module type S2 = sig
    include Monad_trans.S2
    include Monad.S2 with type ('a, 'b) t := ('a, 'b) t
  end

  type ('a, 'b) t = ('a, 'b, 'b) Indexed_continuation.t

  include
    S2
      with type ('a, 'b) t := ('a, 'b) t
       and type ('a, 'b) m := ('a -> 'b) -> 'b
       and type ('a, 'b) e := ('a -> 'b) -> 'b
end *)