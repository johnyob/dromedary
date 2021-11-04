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
       graph). Thus the interface defines implementation behavior. BAD!
     
     - Cannot recompute quantified variables after generalization (due to mutated data).
       This doesn't fit well with notions of higher-rank polymorphism.  

     Requirements of  solution:
     
     - Quantified variables are re-computable in any given level
     
     - Representation mimics "graphic types"*)

  (* Solution:
     
     To re-compute generic variables, we need 2 pieces of information,
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
      
     This removes the notion of a "generic level" (used within the OCaml type 
     checker). Our actual representation is optimized (but provides a similar 
     interface to the one above). *)

  type level = int [@@deriving sexp_of]

  let outermost_level = 0

  (* To merge two arbitrary levels, we take their minimum. *)

  let merge_level = min

  (* ----------------------------------------------------------------------- *)

  (* Tags *)

  (* See above discussion for the motiviation of tags. *)

  module Tag = struct
    exception Generic_mutation

    type t =
      { mutable level : level
      ; mutable is_generic : bool
      }
    [@@deriving sexp_of]

    (* TODO: Add additional information to the exception. *)
    let merge t1 t2 =
      if t1.is_generic || t2.is_generic then raise Generic_mutation;
      { level = merge_level t1.level t2.level; is_generic = false }


    let set_level t level =
      if t.is_generic then raise Generic_mutation;
      t.level <- level


    let get_level t = t.level
    let is_generic t = t.is_generic
    let lift t = t.is_generic <- true
  end

  (* ----------------------------------------------------------------------- *)

  (* Instantiating the unifier with level metadata. *)

  module Unifier = Unifier.Make (Former) (Tag)

  (* Alias, used throughout code below *)
  module U = Unifier

  let set_level typ level = Tag.set_level (U.Type.get_metadata typ) level
  let get_level typ = Tag.get_level (U.Type.get_metadata typ)

  let update_level typ level = if level < get_level typ then set_level typ level
  
  let is_generic typ = Tag.is_generic (U.Type.get_metadata typ)

  let is_generic_at typ level =
    let tag = U.Type.get_metadata typ in
    Tag.is_generic tag && Tag.get_level tag = level


  let lift typ = Tag.lift (U.Type.get_metadata typ)

  let fresh_var flexibility level =
    U.fresh_var flexibility { level; is_generic = false }


  let fresh_form form level = U.fresh_form form { level; is_generic = false }

  (* ----------------------------------------------------------------------- *)

  (* A scheme in "graphic types" simply consists of a node w/ a pointer
     to a graphic type node. 
     
     For generalization and levels, we add the notion of the "bound level"
     to a scheme node within the graphic type. 
     
     Graphic type nodes are marked generic if they are variables
     and their level >= the bound level. The notion of the bound 
     level also allows for the reconstruction of all quantified
     variables within the type. *)

  type scheme =
    { root : U.Type.t
    ; level : level
    }

  (* ----------------------------------------------------------------------- *)

  (* Generalization regions *)

  (* Types (and variables) are partitioned into distincted regions,
     each region related to the stack frame of the type (See levels). 
     
     This allows us to update levels in a lazy manner, as described
     here: ??. 
     
     When we unify two variables, we merge their levels, however, we 
     do not propagate this throughout the type. We perform this update
     on levels at generalization (after occurs checks). 
     
     To perform this update, we need regions to keep track of
     the nodes w/ a given level. *)

  type region = U.Type.t Hash_set.t

  (* ----------------------------------------------------------------------- *)

  (* Generalization state *)

  (* We have two elements of persistent state in generalization.
     
     The current level (the number of stack frames) and the regions (1 for 
     each current stack frame). Hence the length of regions is bounded by 
     the current level. *)

  (* The current number of stack frames. *)

  let current_level : level ref = ref outermost_level

  (* Active regions. *)

  let regions : (region, [ `R | `W ]) Vec.t = Vec.make ()

  (* ----------------------------------------------------------------------- *)

  (* [enter ()] creates a new stack frame and enter it. *)

  let enter () =
    Int.incr current_level;
    Vec.set_exn regions !current_level (Hash_set.create (module U.Type))

  (* [exit ()] exits the current stack frame. *)

  let exit () =
    Int.decr current_level

  (* ----------------------------------------------------------------------- *)
  
  (* Region management. *)
  
  (* [set_region typ] adds [typ] to it's region (defined by [typ]'s level). *)

  let set_region typ = Hash_set.add (Vec.get_exn regions (get_level typ)) typ

  (* When performing region updates, we often only care about maintaing
     and update nodes within the "young" region (the current region),
     leaving updates in older regions to later phases of generalization. *)

  (* [is_young typ] determines whether [typ] is in the young region. *)

  let is_young typ = Hash_set.mem (Vec.get_exn regions !current_level) typ

  (* [young_region] returns the "young" region. *)

  let young_region () = Vec.get_exn regions !current_level

  (* ----------------------------------------------------------------------- *)

  (* Generalization *)

  (* Generalization performs two functions:
      1) Propagate delayed level updated to nodes
      2) Generalize variables or update regions of variables
      3) Clear the current region
      
     As such, these phases have been split into the following
     relevant functions:
      1) [update_levels]
      2) [update_regions]
      3) [generalize]
      
     See below for documentation of the various functions. *)

  (* [update_levels] updates the levels of all types within the 
     young region. 
     
     It traverses all nodes (as roots) from the young generation, 
     using a depth-frst traversal. The traversal stops when we 
     reach nodes within the old region. 

     This function assumes that all types within the current region
     are acyclic (a problem!)

     Moreover this function visited nodes multiple times! 
     
     The point of update levels is to ensure that every 
     node within young generation has it's correct level. *)

  (* TODO: 
  
     Observe: Levels only decrease => processing nodes in a level
     order ensures a partial order within updated nodes! 
     
     Flesh this idea out more! *)

  let update_levels () =
    let rec loop typ level =
      (* Regardless of whether a node is young or old, 
         we update it's level. *)
      update_level typ level;
      (* If a node is old, then we stop traversing (hence the [is_young] check). *)
      if is_young typ
      then (
        match U.Type.get_structure typ with
        | U.Type.Var _ -> 
          (* In the variable case, we cannot traverse any further
             and no updates need be performed (since the level update)
             is performed above. *)
          ()
        | U.Type.Form form ->
          (* If the node is a type former, then we need to traverse it's 
             children and determine it's correct level.
             
             Levels must satisfy the following monotonicty condition:
             get_level typ <= k => get_type typ' <= k where typ' is a 
             child of typ. 
             
             Thus we take the [max] of children with [outermost_level]
             being our unit element. *)
          update_level
            typ
            (Former.fold
               form
               ~f:(fun typ acc ->
                 loop typ level;
                 max (get_level typ) acc)
               ~init:outermost_level))
    in
    young_region ()
    |> Hash_set.iter ~f:(fun typ -> 
      (* Perform occurs check *)
      U.occurs_check typ;
      (* Then traverse using [loop] *)
      loop typ (get_level typ)) 
  
  (* [update_regions] updates the regions according to the new levels
     propagated by [update_levels].
     
     If a node has a level < !current_level, then it belongs in an 
     older region. It is moved using [set_region].
     
     Otherwise, if the node has level = !current_level, then it may 
     be generalized, using [lift]. *)
  let update_regions () =
    Hash_set.iter (young_region ()) ~f:(fun typ ->
        if get_level typ < !current_level then set_region typ else lift typ)

  let generalize typ =
    U.occurs_check typ;
    update_levels ();
    update_regions ();
    Hash_set.clear (Vec.get_exn regions !current_level);
    { root = typ; level = !current_level } 


  (* ----------------------------------------------------------------------- *)

  (* The notion of variables is common in schemes, especially 
     instantiation. 
     
     It is also used in [generic_variables], which returns the generic
     variables of a scheme. 
     
     We use [Hash_set] implementation, since ordering does not matter. *)

  type variables =
    { flexible : U.Type.t Hash_set.t
    ; rigid : U.Type.t Hash_set.t
    }

  let[@inline] add_variable variables flexibility typ =
    (* TODO: Add assertion for variable structure *)
    let variable_set =
      match flexibility with
      | U.Type.Flexible -> variables.flexible
      | U.Type.Rigid -> variables.rigid
    in
    Hash_set.add variable_set typ


  let[@inline] empty_variables () =
    { flexible = Hash_set.create (module U.Type)
    ; rigid = Hash_set.create (module U.Type)
    }


  (* ----------------------------------------------------------------------- *)

  let root { root; _ } = root

  let generic_variables { root; level } =
    (* Hash set records whether we've visited a given 
       graphic type node. Prevents cyclic execution of [loop]. *)
    let visited : U.Type.t Hash_set.t = Hash_set.create (module U.Type) in
    let generic_variables = empty_variables () in
    let rec loop typ =
      (* A type [typ] contains a generic variable if it is generic
         w/ level [level]. *)
      if is_generic_at typ level && not (Hash_set.mem visited typ)
      then (
        (* We mark node visited here to ensure that 
           when we recurse below, we don't reach an infinite loop
           due to cycles in [root]. *)
        Hash_set.add visited typ;
        (* Check the structure of the type [typ]. 
           If [Var], add to the relevant quantifier list,
           otherwise recurse.  *)
        match U.Type.get_structure typ with
        | U.Type.Var { flexibility } ->
          add_variable generic_variables flexibility typ
        | U.Type.Form form -> Former.iter ~f:loop form)
    in
    loop root;
    generic_variables


  (* ----------------------------------------------------------------------- *)

  (* When instantiating a scheme [scheme], we must traverse it's body, 
    creating new (copied) variables for each generic variable, returning 
    the new root and new variables.
  
    This is equivalent to the theortical notion of a "substitution". *)

  let instantiate { root; level } =
    (* The [copied] hash table stores a mapping from graphic type nodes 
        to their related copied forms. This ensures only 1 copy per 
        variable. *)
    let copied : (U.Type.t, U.Type.t) Hashtbl.t =
      Hashtbl.create (module U.Type)
    in
    (* We also need to keep track of the instantiated variables,
       using a [instance variables] record. *)
    let instance_variables = empty_variables () in
    (* We traverse the type, if it is generic, then we copy it
       and recursivly traverse. Otherwise, we return the type 
       as is. *)
    let rec copy typ =
      (* We use [is_generic] instead of [is_generic_at],
         since we may have to copy generic variables that
         have been generalized by a different scheme. *)
      if not (is_generic typ)
      then typ
      else (
        try Hashtbl.find_exn copied typ with
        | Not_found_s _ ->
          (* Create arbitrary node. We use a variable initially,
             but will set the structure later on. See below. *)
          let typ' = fresh_var Flexible !current_level in
          (* We set the region of the type [typ']. This
             will add it to the current region (due to a
             level of [!current_level]).
             
             We also set the mapping from [typ] to [typ']
             in copied. *)
          set_region typ';
          Hashtbl.set copied ~key:typ ~data:typ';
          (* We now update the structure according to the original 
             structure of [typ].  *)
          let structure' =
            match U.Type.get_structure typ with
            | U.Type.Var { flexibility } ->
              (* The condition [get_level typ = level] now asserts
                 [is_generic_at typ level], hence we need to instantiate
                 the variable, adding it to the instance variables. *)
              if get_level typ = level
              then add_variable instance_variables flexibility typ';
              U.Type.Var { flexibility }
            | U.Type.Form form -> U.Type.Form (Former.map ~f:copy form)
          in
          U.Type.set_structure typ' structure';
          typ')
    in
    (* Copy the root, yielding the instance variables (as a side-effect). *)
    instance_variables, copy root
end
