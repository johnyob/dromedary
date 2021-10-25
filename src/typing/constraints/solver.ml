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

(* This module implements a constraint solver, based on unification
   under a mixed prefix (rigid variables). *)

open Base
open Intf

(* ------------------------------------------------------------------------- *)

module Make (Term_var : Term_var) (Types : Types) = struct
  (* ----------------------------------------------------------------------- *)

  (* Instantiate the constraints definition *)

  module Constraint = Constraint.Make (Term_var) (Types)

  (* ----------------------------------------------------------------------- *)

  (* Generalization. *)

  (* Levels *)

  (* We implement efficient level-based generalization by Remy [??]. 
    Each unification variable has a "level" (or "rank"). 
    
    Each variable within the current scope (stack frame [S])
    has a level, with the outermost level being 0. The level is isomorphic to a 
    de Bruijn level, namely, when we [cst1] in 
    [let a1 ... an [cst1] (x1: a1 and ... and xn: an)], we increment the level 
    by 1. 
    
    Variables not within the current scope, but within the environment frame,
    has the level [generic]. *)

  (* As opposed to the traditional int representation, we use an [int option]. 
     This allows us to distinguish between levels and no-levels. *)

  type level = int

  let merge = min

  (* As opposed to using a really large number, as suggested here: Oleg [??],
     Our generic level is level < 0. This also fits better w/ our stack frame 
     formalization. *)
  let generic_level = -1

  (* Positive levels are all valid (non-generic) levels. *)
  let base_level = 0

  (* Mapping a level to each variable consists of adding it to
     the variable's mutable metadata.  *)

  module Level_metadata = struct
    type t = level

    let sexp_of_t = Int.sexp_of_t
    let merge = merge
  end

  (* Instantiating the unifier with level metadata. *)

  module U = Unifier.Make (Types.Former) (Level_metadata)

  (* Wrappers on existing unifier functions. *)

  let set_level var level = U.set_metadata var level
  let get_level var = U.get_metadata var
  let fresh kind ?terminal level = U.fresh kind ?terminal ~metadata:level

  (* We maintain the current level of the stack frame. *)

  let current_level : level ref = ref base_level

  (* [enter ()] creates a new stack frame and enter it. *)

  let enter () = Int.incr current_level

  (* [exit ()] exits the current stack frame. *)

  let exit () = Int.decr current_level

  (* ----------------------------------------------------------------------- *)

  (* Generalization and instantiation *)

  (* Our internal notion of a type scheme is a list of variables,
     known as quantified variables and a body (a variable). 
     
     The list of variables are "generic". *)

  type scheme = U.variable list * U.variable


  let generalize var =
    (* Before generalizing a type, we perform an occurs check.
     
     This ensures that [var] is acyclic and also ensures soundness
     of generalization. *)
    U.occurs_check var;
    (* When generalizing, we traverse the variable,
     determining the set of "generalizable" variables. 
     
     A variable is generalizable if it's level >= the current level
     and it has no terminal. 
     
     Ideally would prefer to implement this traversal using
     [U.fold], but implementation relied on (@) (very slow!). *)
    let quantified_variables =
      let visited : U.variable Hash_set.t =
        Hash_set.create (module U.Variable_hash_key)
      in
      let rec loop var acc =
        if (not (get_level var > !current_level)) || Hash_set.mem visited var
        then acc
        else (
          Hash_set.add visited var;
          match U.get_terminal var with
          | None ->
            set_level var generic_level;
            var :: acc
          | Some t -> Types.Former.fold t ~f:loop ~init:acc)
      in
      loop var []
    in
    quantified_variables, var


  (* When instantiating a scheme [scheme], we must traverse it's body, 
    creating new (copied) variables for each generic variable, returning 
    the new body and new variables.
    
    This is equivalent to the theortical notion of a "substitution". *)

  let instantiate scheme =
    match scheme with
    | [], body ->
      (* No generic quantified variables, return the scheme as-is. *)
      [], body
    | quantified_variables, body ->
      (* The [copied] hash table stores a mapping from variables to their
         related copied variables. This ensures only 1 copy per variable. *)
      let copied : (U.variable, U.variable) Hashtbl.t =
        Hashtbl.create (module U.Variable_hash_key)
      in
      (* We traverse the variable, if it is generic, then we copy it
         and recursivly traverse. Otherwise, we return the variable 
         as is. *)
      let rec loop var =
        if get_level var <> generic_level
        then var
        else (
          try Hashtbl.find_exn copied var with
          | Not_found_s _ ->
            let var' = fresh (U.kind var) !current_level () in
            U.set_terminal
              var'
              (Option.map (U.get_terminal var) ~f:(Types.Former.map ~f:loop));
            Hashtbl.set copied ~key:var ~data:var';
            var')
      in
      (* Copy the quantified variables, then the body to instantiate the 
         sceheme. *)
      List.map ~f:loop quantified_variables, loop body

  (* ----------------------------------------------------------------------- *)


end
