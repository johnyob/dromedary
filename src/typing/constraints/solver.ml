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

(* This module implements a constraint solver and term elaborator,
   based on F. Pottier's paper ??. *)

open Base
open Intf

(* ------------------------------------------------------------------------- *)

module Make (Term_var : Term_var) (Types : Types) = struct
  (* ----------------------------------------------------------------------- *)

  module C = Constraint.Make (Term_var) (Types)
  module G = Generalization.Make (Types.Former)
  module U = G.Unifier

  (* ----------------------------------------------------------------------- *)

  (* Applicative structure used for elaboration. *)

  module Elaborate = struct
    type 'a t = unit -> 'a

    let run t = t ()
    let return x () = x
    let map t ~f () = f (t ())
    let both t1 t2 () = t1 (), t2 ()

    module Let_syntax = struct
      module Let_syntax = struct
        let return = return
        let map = map
        let both = both
      end
    end
  end

  (* ----------------------------------------------------------------------- *)

  (* An environment in our constraint solver is defined as a 
     partial finite function from term variables to schemes. 
     
     We implement this using a [Map]. 
     
     We favor [Map] over [Hashtbl] here since we want immutability 
     for recursive calls, as modifications in a local block shouldn't
     affect the overall environment 

     e.g. let x : 'a ... 'b. [ let y : 'c ... 'd. [ C ] in C' ] in C'',
     here binding y shouldn't affect the environment for C''. 
     This would not be the case for a mutable mapping (using side-effecting
     operations). 
     
     Using [Hashtbl] would implement a dynamically scoped environment
     as opposed to a lexically scoped one. *)

  module Term_var_comparator = Comparator.Make (Term_var)

  type env =
    (Term_var.t, G.scheme, Term_var_comparator.comparator_witness) Map.t

  (* ----------------------------------------------------------------------- *)

end
