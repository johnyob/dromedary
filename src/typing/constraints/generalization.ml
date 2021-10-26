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

(* This module implements a notion of generalization based on "graphic 
   types". *)

open Base
open Intf

module Make (Former : Type_former) = struct
  (* ----------------------------------------------------------------------- *)

  (* Levels *)

  (* We implement efficient level-based generalization by Remy [??].
  
     In theory, each unification variable has a "level" (or "rank").
     Each variable with the current scope (stack frame [S]) has a level, 
     with the outermost level being 0. This is isomorphic to a de Bruijn
     level, denoting the number of binders (stack frames). 

     Variables not within the current scope, but within the environment
     frame are "generic".

     We use the efficient presentation from Oleg's blog post ??,
     taking a "lazy" approach. Hence each node within the graphic type
     stores a level, this allows us to delay the propagation of levels 
     to generalization. *)

  (* Our approach differs compared the approach describe by Oleg.
     There are several problems with representing a "scheme"
     as a type with some quantified variables (determined at generalization).

     Problems:

     - Representation of [var list * type] relies on the invariant that
       all pointers in the var list are indeed variables (our implementation
       doesn't allow this to be distinguished at the type level), and would
       indeed rely on invariants.  

     - We must generalize immediately after exiting (due to mutable data in 
       graph). Thus interface defines implementation behavior. BAD!
     
     - TODO: DOCUMENT OTHER PROBLEMS 
     
     Requirements of  solution:
     
     - Quantified variables are re-computable in any given level
     
     - Representation mimics "graphic types"*)

  (* Solution:
     
     To re=compute generic variables, we need 2 pieces of information,
     the level of scheme and the level of every variable (including generic 
     ones). 

     Thus we store the level of the scheme in the representation of [scheme]
     and each generic variable keeps the level it initially had (prior to 
     generalization). 

     To distinguish between generic and non-generic (instance) variables w/ levels, 
     we use a tagged sum-type:
     
     type tag = 
      | Instance of { mutable level: level }
      | Generic of level 
      
      This removes the notion of a "generic level". 
      
      TODO: Investigate performance (run benchmark). 
      Consider unboxing? *)

  type level = int [@@deriving sexp_of]

  (* To merge two arbitrary levels, we take their minimum. *)

  let merge_level = min

  (* ----------------------------------------------------------------------- *)

  (* Tags *)

  (* See above discussion for the motiviation of tags. *)

  module Tag = struct
    exception Generic_mutation 

    type t =
      | Instance of { mutable level : level }
      | Generic of level
    [@@deriving sexp_of]

    (* TODO: Add additional information to the exception. *)
    let merge t1 t2 =
      match t1, t2 with
      | Instance { level = l1 }, Instance { level = l2 } ->
        Instance { level = merge_level l1 l2 }
      | _, _ -> raise Generic_mutation

    let set_level t level' = 
      match t with
      | Instance level -> level.level <- level'
      | Generic _ -> raise Generic_mutation

    let get_level t = 
      match t with
      | Instance { level } -> level
      | Generic level -> level

    let lift t = 
      match t with
      | Instance { level } -> Generic level 
      | _ -> t

  end


  (* ----------------------------------------------------------------------- *)

  (* Instantiating the unifier with level metadata. *)

  module U = Unifier.Make (Former) (Tag)

  let set_level typ level = Tag.set_level (U.Type.get_metadata typ) level

  let get_level typ = Tag.get_level (U.Type.get_metadata typ)

  (* TODO: Consider replacing set w/ update => set is now a derived 
     operator? *)

  let lift typ = U.Type.set_metadata typ (Tag.lift (U.Type.get_metadata typ))

  let fresh_var flexibility level = U.fresh_var flexibility (Instance { level })

  (* ----------------------------------------------------------------------- *)

  (* Generalization state *)

  (* We maintain the current level of the stack frame. *)

  let current_level = ref 0

  (* [enter ()] creates a new stack frame and enter it. *)

  let enter () = 
    Int.incr current_level

  (* [exit ()] exits the current stack frame. *)

  let exit () = 
    Int.decr current_level

  (* ----------------------------------------------------------------------- *)

  (* Generalization and instantiation *)

  (* TODO: Document! *)

  type scheme = { t : U.Type.t; level: level }




end
