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

module Monad_trans = struct
  module type S1 = sig

  end

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
end = struct
  module type S2 = sig
    include Monad_trans.S2

    type state

    val write : state -> (unit, 'b) t
    val read : ('a, 'b) t -> (state, 'b) t
    val listen : ('a, 'b) t -> (state * 'a, 'b) t

    include Monad.S2 with type ('a, 'b) t := ('a, 'b) t
  end

  type ('state, 'a) writer = 'state * 'a

  module Make2 (State : Monoid) (M : Monad.S2) = struct
    type ('a, 'b) t = ((State.t, 'a) writer, 'b) M.t

    open M.Let_syntax

    module Basic = struct
      type nonrec ('a, 'b) t = ('a, 'b) t

      let bind t ~f =
        let%bind state1, x = t in
        let%bind state2, y = f x in
        return (State.plus state1 state2, y)


      let return x = return (State.zero, x)
      let map = `Custom (fun t ~f -> t >>| fun (state, x) -> state, f x)
    end

    let write state = return (state, ())
    let read t = t >>| fun (state, _) -> state, state
    let listen t = t >>| fun (state, x) -> state, (state, x)
    let run t = t
    let lift t = t >>| fun x -> State.zero, x

    include Monad.Make2 (Basic)
  end
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
end = struct
  module type S2 = sig
    include Monad_trans.S2

    type state

    val read : unit -> (state, 'a) t
    val local : ('a, 'b) t -> f:(state -> state) -> ('a, 'b) t

    include Monad.S2 with type ('a, 'b) t := ('a, 'b) t
  end

  type ('state, 'a) reader = 'state -> 'a

  module Make2 (T : T) (M : Monad.S2) = struct
    type ('a, 'b) t = (T.t, ('a, 'b) M.t) reader

    open M.Let_syntax

    module Basic : Monad.Basic2 with type ('a, 'b) t = ('a, 'b) t = struct
      type nonrec ('a, 'b) t = ('a, 'b) t

      let bind t ~f state =
        let%bind x = t state in
        f x state


      let return x _ = return x
      let map = `Custom (fun t ~f state -> t state >>| f)
    end

    let lift t _ = t
    let run t state = t state
    let read () state = return state
    let local t ~f state = t (f state)

    include Monad.Make2 (Basic)
  end
end

module Indexed_continuation = struct

  type ('a, 'i, 'j) t = ('a -> 'j) -> 'i

  include Monad.Make_indexed (struct
    type nonrec ('a, 'i, 'j) t = ('a, 'i, 'j) t

    let return x k = k x
    let bind t ~f = fun k -> t (fun a -> f a k)
    let map = `Define_using_bind
  end)

  let lift t = t

  let run t = t

end

module Continuation = struct

  module type S1 = sig
    include Monad_trans.S1
    include Monad.S1 with type 'a t := 'a t
  end

  module type S2 = sig
    include Monad_trans.S2
    include Monad.S2 with type ('a, 'b) t := ('a, 'b) t
  end

  type ('a, 'b) t = ('a, 'b, 'b) Indexed_continuation.t

  include Monad.Make2 (struct
    type nonrec ('a, 'b) t = ('a, 'b) t

    let return x k = k x
    let bind t ~f = fun k -> t (fun a -> f a k)
    let map = `Define_using_bind
  end)

  let lift t = t

  let run t = t

end *)
