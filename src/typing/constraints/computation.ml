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
include Computation_intf

module Make (Algebra : Algebra) (Basic : Basic) = struct
  module Constraint = Constraint.Make (Algebra)

  module Computation = struct
    type 'a t = 'a Constraint.t Basic.t

    include Applicative.Make (struct
      type nonrec 'a t = 'a t

      open Applicative.Of_monad (Basic)

      let return x = return (Constraint.return x)
      let apply t1 t2 = apply (map t1 ~f:Constraint.apply) t2
      let map = `Custom (fun t ~f -> map t ~f:(Constraint.map ~f))
    end)

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
  end

  open Computation

  let lift t = t
  let run t = t

  let constraint_ = Basic.return
  let const = return
  let pure c ~f = constraint_ (Constraint.map c ~f)

  module Let_syntax = struct
    let return = constraint_
    let ( >>| ) = Constraint.( >>| )
    let ( <*> ) = Constraint.( <*> )

    module Let_syntax = struct
      let return = return
      let map = Constraint.map
      let both = Constraint.both
      let sub ?here:_ t ~f = Basic.bind t ~f
      let arr ?here:_ t ~f = pure t ~f
    end
  end
end

module Make2 (Algebra : Algebra) (Basic : Basic2) = struct
  module Constraint = Constraint.Make (Algebra)

  module Computation = struct
    type ('a, 'b) t = ('a Constraint.t, 'b) Basic.t

    include Applicative.Make2 (struct
      type nonrec ('a, 'b) t = ('a, 'b) t

      open Applicative.Of_monad2 (Basic)

      let return x = return (Constraint.return x)
      let apply t1 t2 = apply (map t1 ~f:Constraint.apply) t2
      let map = `Custom (fun t ~f -> map t ~f:(Constraint.map ~f))
    end)

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
  end

  open Computation

  let lift t = t
  let run t = t

  let constraint_ = Basic.return
  let const = return
  let pure c ~f = constraint_ (Constraint.map c ~f)

  module Let_syntax = struct
    let return = constraint_
    let ( >>| ) = Constraint.( >>| )
    let ( <*> ) = Constraint.( <*> )

    module Let_syntax = struct
      let return = return
      let map = Constraint.map
      let both = Constraint.both
      let sub ?here:_ t ~f = Basic.bind t ~f
      let arr ?here:_ t ~f = pure t ~f
    end
  end
end
