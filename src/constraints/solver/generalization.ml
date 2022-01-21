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

open! Import

(* Include module types and type definitions from the [_intf] file. *)

include Generalization_intf
open Structure

module Make (Former : Type_former.S) = struct
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
     to generalization. 
  *)

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
     
     - Cannot recompute quantified variables after generalization (due to 
       mutated data). This doesn't fit well with notions of 
       higher-rank polymorphism.  

     Requirements of  solution:
     
     - Quantified variables are re-computable in any given level
     
     - Representation mimics "graphic types"
  *)

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
     interface to the one above). 
  *)

  type level = int [@@deriving sexp_of]

  let outermost_level = 0

  (* [merge_level l1 l2] merges levels [l1] and [l2]. To merge two arbitrary 
     levels, we take their minimum. *)
  let merge_level = min

  module Ambivalent = Ambivalent (Structure.Of_former (Former))

  module Structure = struct
    type 'a t =
      { mutable structure : 'a Ambivalent.t
      ; mutable level : int
      ; mutable is_generic : bool
      }
    [@@deriving sexp_of]

    let former t = Ambivalent.structure t.structure
    let rigid_vars t = Ambivalent.rigid_vars t.structure
    let scope t = Ambivalent.scope t.structure

    let update_scope t scope =
      t.structure <- Ambivalent.update_scope t.structure scope


    let level t = t.level
    let update_level t level = if level < t.level then t.level <- level
    let is_generic t = t.is_generic
    let is_generic_at t level = t.is_generic && t.level = level
    let generalize t = t.is_generic <- true

    (* let set_former t former = t.structure <- Ambivalent.set_structure t.structure former *)
    let map t ~f = { t with structure = Ambivalent.map t.structure ~f }
    let iter t ~f = Ambivalent.iter t.structure ~f
    let fold t ~f ~init = Ambivalent.fold t.structure ~f ~init

    exception Cannot_merge

    type 'a expansive = { make : 'a Ambivalent.t -> 'a }
    type ctx = Ambivalent.Equations.Ctx.t

    let merge ~expansive ~ctx ~equate t1 t2 =
      assert (not (t1.is_generic || t2.is_generic));
      (try
         t1.structure
           <- Ambivalent.merge
                ~expansive:
                  { make = (fun structure -> expansive.make structure)
                  ; sexpansive = ()
                  }
                ~ctx:(ctx, ())
                ~equate
                t1.structure
                t2.structure
       with
      | Ambivalent.Cannot_merge -> raise Cannot_merge);
      update_level t1 t2.level;
      t1
  end

  module Unifier = Unifier.Make (Structure)

  (* [U] and [A] are aliases, used for a short prefix below. *)
  module U = Unifier

  let former type_ = U.Type.get_structure type_ |> Structure.former
  let get_rigid_vars type_ = U.Type.get_structure type_ |> Structure.rigid_vars
  let level type_ = U.Type.get_structure type_ |> Structure.level
  let scope type_ = U.Type.get_structure type_ |> Structure.scope
  let is_generic type_ = U.Type.get_structure type_ |> Structure.is_generic

  let is_generic_at type_ level =
    Structure.is_generic_at (U.Type.get_structure type_) level


  (* [generalize_type type_] generalizes the type [type_]. *)
  let generalize_type type_ = U.Type.get_structure type_ |> Structure.generalize

  let update_level type_ level =
    Structure.update_level (U.Type.get_structure type_) level


  let update_scope type_ scope =
    Structure.update_scope (U.Type.get_structure type_) scope


  (* let set_former type_ former = Structure.set_former (U.Type.get_structure type_) former *)

  (* [make_var_] and [make_former_] are internal functions for making type 
     variables and type formers wrapping [Unifier]. *)

  let make_flexible_var_ level =
    U.Type.make
      { structure = Ambivalent.make_structure None; level; is_generic = false }


  let make_rigid_var_ rigid_var level =
    U.Type.make
      { structure = Ambivalent.make_rigid_var rigid_var
      ; level
      ; is_generic = false
      }


  let make_former_ former level =
    U.Type.make
      { structure = Ambivalent.make_structure (Some former)
      ; level
      ; is_generic = false
      }


  (* Generalization regions
  
     Types (and variables) are partitioned into distincted regions,
     each region related to the stack frame of the type (See levels). 
     
     This allows us to update levels in a lazy manner, as described
     here: ??. 
     
     When we unify two variables, we merge their levels, however, we 
     do not propagate this throughout the type. We perform this update
     on levels at generalization (after occurs checks). 
     
     To perform this update, we need regions to keep track of
     the nodes w/ a given level. 
  *)

  type region = U.Type.t Hash_set.t

  (* State
  
     We have two elements of persistent state in generalization.
     
     The current level (the number of stack frames) and the regions (1 for 
     each current stack frame). Hence the length of regions is bounded by 
     the current level. 

     Invariant: [length regions = current_level + 1]
  *)

  type state =
    { mutable current_level : level
    ; regions : (region, [ `R | `W ]) Vec.t
    }

  (* [make_state ()] makes a new empty state. *)

  let make_state () =
    { current_level = outermost_level - 1; regions = Vec.make () }


  module Rigid_type = struct
    type t = Ambivalent.Rigid_type.t

    let make_var rigid_var = Ambivalent.Rigid_type.Rigid_var rigid_var
    let make_former former = Ambivalent.Rigid_type.Structure former
  end

  module Equations = struct
    type t = Ambivalent.Equations.Ctx.t

    let empty = Ambivalent.Equations.Ctx.empty

    exception Inconsistent = Ambivalent.Equations.Ctx.Inconsistent

    let add state t rigid_type1 rigid_type2 =
      Ambivalent.Equations.Ctx.add t rigid_type1 rigid_type2 state.current_level
  end

  let pp_type_explicit type_ =
    let rec pp_type_explicit type_ =
      U.Type.get_structure type_ |> Structure.sexp_of_t pp_type_explicit
    in
    Caml.Format.printf "%s\n" (Sexp.to_string_mach (pp_type_explicit type_))


  let pp_type type_ =
    Caml.Format.printf
      "id = %d, level = %d is_generic = %b, scope = %d\n"
      (U.Type.id type_)
      (level type_)
      (is_generic type_)
      (scope type_)


  let pp_region i region =
    Caml.Format.printf "Region %d\n" i;
    Hash_set.iter
      ~f:(fun type_ ->
        pp_type type_;
        pp_type_explicit type_)
      region


  let pp_regions state = Vec.iteri pp_region state.regions

  let pp_current_level state =
    Caml.Format.printf "Current level: %d\n" state.current_level


  let pp_state state debug_label =
    Caml.Format.printf "%s:\n" debug_label;
    pp_current_level state;
    pp_regions state


  (* [set_region type_] adds [type_] to it's region (defined by [type_]'s level). *)

  let set_region state type_ =
    (* Stdio.print_string "set_region"; *)
    Hash_set.add (Vec.get_exn state.regions (level type_)) type_


  let make state structure = 
    let new_type = U.Type.make { structure; level = state.current_level; is_generic = false} in
    set_region state new_type;
    new_type

  (* [make_var] creates a fresh unification variable, setting it's level
     and region. *)

  let make_flexible_var state =
    let var = make state (Ambivalent.make_structure None) in
    Caml.Format.printf "New variable:\n";
    pp_type var;
    var


  let make_rigid_var state rigid_var =
    let var = make state (Ambivalent.make_rigid_var rigid_var) in
    Caml.Format.printf "New rigid variable: %d\n" (rigid_var :> int);
    pp_type var;
    var


  (* [make_former] creates a fresh unification type node 
     w/ the structure provided by the former [former]. 
      
     It initialize the level to the current level. 
  *)
  let make_former state former =
    let former = make state (Ambivalent.make_structure (Some former)) in
    Caml.Format.printf "New former:\n";
    pp_type former;
    pp_type_explicit former;
    former


  let unify state ~ctx t1 t2 =
    Caml.Format.printf "Unify: %d %d\n" (U.Type.id t1) (U.Type.id t2);
    U.unify ~expansive:{ make = make state } ~ctx t1 t2

  let current_scope state = state.current_level

  (* [enter ()] creates a new stack frame and enter it. *)

  let enter state =
    state.current_level <- state.current_level + 1;
    Vec.push (Hash_set.create (module U.Type)) state.regions


  (* A scheme in "graphic types" simply consists of a node w/ a pointer
     to a graphic type node. 
     
     For generalization and levels, we add the notion of the "bound level"
     to a scheme node within the graphic type. 
     
     Graphic type nodes are marked generic if they are variables
     and their level >= the bound level. The notion of the bound 
     level also allows for the reconstruction of all quantified
     variables within the type. 
  *)

  type scheme =
    { root : U.Type.t
    ; level : level
    }

  (* Region management
  
     When performing region updates, we often only care about maintaing
     and update nodes within the "young" region (the current region),
     leaving updates in older regions to later phases of generalization.
     
     This notion of region corresponds to Oleg's update queue, however, 
     we split this queue into regions (so we don't need to traverse the
     entire queue when updating).
  *)

  (* [young_region state] returns the "young" region in [state] *)

  let young_region state =
    (* Stdio.print_string "young_region"; *)
    Vec.get_exn state.regions state.current_level


  (* [is_young state type_] determines whether [type_] is in the young region. 
     Optimized for many executions for a given state. *)
  let is_young state =
    let young_region =
      (* TODO: Make this more efficient. Could use hashtbl. *)
      Hash_set.of_list
        (module Int)
        (young_region state |> Hash_set.to_list |> List.map ~f:U.Type.id)
    in
    fun type_ ->
      let result = Hash_set.mem young_region (U.Type.id type_) in
      (* Caml.Format.printf "is young? %d = %b\n" (U.Type.id type_) result; *)
      result


  (* Generalization performs 4 functions:
      1) Propagate delayed level updated to nodes
      2) Check no rigid variables have escpaed
      3) Generalize variables or update regions of variables
      4) Clear the current region
      
     As such, these phases have been split into the following
     relevant functions:
      1) [update_levels]
      2) [update_regions]
      3) [generalize]
      
     See below for documentation of the various functions. 
  *)

  (* [update_levels state] updates the levels of all types within the 
     young region of [state]. 
     
     It traverses all nodes (as roots) from the young generation, 
     using a depth-first traversal. The traversal stops when we 
     reach nodes within the old region. 

     Historically: This function assumed that all types 
     within the current region were acyclic (a problem!)
     Moreover this function visited nodes multiple times! 
     The point of update levels is to ensure that every 
     node within young generation has it's correct level. 
     
     However, we now visit nodes in order of increasing levels,
     since levels can only decrease, it follows that we only need to visit
     nodes once (defining a partial order).    
  *)

  let update_scopes state =
    (* [is_young state type_] determines whether [type_] is in the young region. *)
    let is_young = is_young state in
    let young_region = young_region state |> Hash_set.to_array in
    (* Order the young region in highest to lowest scopes. *)
    Array.sort young_region ~compare:(fun t1 t2 ->
        -Int.compare (scope t1) (scope t2));
    Caml.Format.printf "Scope Array order:\n";
    Caml.Format.printf
      "%s\n"
      (Array.to_list young_region
      |> List.map ~f:(fun t -> Int.to_string (U.Type.id t))
      |> String.concat ~sep:",");
    (* Hash set records whether we've visited a given 
       graphic type node. Prevents cyclic execution of [loop]. *)
    let visited : U.Type.t Hash_set.t = Hash_set.create (module U.Type) in
    let rec loop type_ scope =
      if not (Hash_set.mem visited type_)
      then (
        Hash_set.add visited type_;
        update_scope type_ scope;
        if is_young type_
        then
          U.Type.get_structure type_
          |> Structure.iter ~f:(fun type_ -> loop type_ scope))
    in
    Array.iter ~f:(fun type_ -> loop type_ (scope type_)) young_region


  exception Scope_escape of U.Type.t

  let update_levels state =
    (* We note that levels only decrease (since we take the minimum when merging),
       hence we process nodes in level order. 
       
       This allows us to only visit each node once, providing the invariant that 
       at the current level [level], all nodes visited are of level [<= level]. 
       
       To implement this, we convert the young region into a sorted array
       which we iterate over to begin the traversal. *)
    (* [is_young state type_] determines whether [type_] is in the young region. *)
    let is_young = is_young state in
    let young_region = young_region state |> Hash_set.to_array in
    Array.sort young_region ~compare:(fun t1 t2 ->
        Int.compare (level t1) (level t2));
    Caml.Format.printf "Array order:\n";
    Caml.Format.printf
      "%s\n"
      (Array.to_list young_region
      |> List.map ~f:(fun t -> Int.to_string (U.Type.id t))
      |> String.concat ~sep:",");
    (* Hash set records whether we've visited a given 
       graphic type node. Prevents cyclic execution of [loop]. *)
    let visited : U.Type.t Hash_set.t = Hash_set.create (module U.Type) in
    let rec loop type_ level' =
      if not (Hash_set.mem visited type_)
      then (
        (* Mark as visited first. This is required with graphic types
           containing cycles. Allows us to reduce # of occurs checks. *)
        Hash_set.add visited type_;
        (* Regardless of whether a node is young or old, 
          we update it's level. *)
        update_level type_ level';
        (* If a node is old, then we stop traversing (hence the [is_young] check). *)
        if is_young type_
        then (
          match former type_ with
          | None ->
            (* In the variable case, we cannot traverse any further
              and no updates need be performed (since the level update)
              is performed above. 
            *)
            ()
          | Some former ->
            (* If the node is a type former, then we need to traverse it's 
              children and determine it's correct level.
              
              Levels must satisfy the following monotonicty condition:
              get_level typ <= k => get_type typ' <= k where typ' is a 
              child of typ. 
              
              Thus we take the [max] of children with [outermost_level]
              being our unit element. 
            *)
            update_level
              type_
              (Former.fold former ~init:outermost_level ~f:(fun type_ acc ->
                   loop type_ level';
                   max (level type_) acc)));
        (* Perform scope check *)
        if level type_ < scope type_
        then (
          Caml.Format.printf
            "Scope escape: id=%d, level=%d, scope=%d\n"
            (U.Type.id type_)
            (level type_)
            (scope type_);
          raise (Scope_escape type_)))
    in
    Array.iter ~f:(fun type_ -> loop type_ (level type_)) young_region


  exception Rigid_variable_escape of Rigid_var.t
  exception Cannot_flexize of Rigid_var.t

  (* [generalize state] generalizes variables in the current
     region according to the new levels propagated by [update_levels].
     
     If a node has a level < !current_level, then it belongs in an 
     older region. It is moved using [set_region].
     
     Otherwise, if the node has level = !current_level, then it may 
     be generalized, using [generalize_type]. 
     
     Once generalized, we compute the list of generalizable
     variables. 
  *)
  let generalize state ~rigid_vars =
    (* Create a mapping between rigid variables and flexible variables for flexization. *)
    let rigid_vars_tbl =
      Hashtbl.of_alist_exn
        (module Rigid_var)
        (List.map rigid_vars ~f:(fun rigid_var ->
             rigid_var, make_flexible_var state))
    in
    (* Get the young region, since we will be performing several traversals
       of it. *)
    let region = young_region state in
    (* Iterate through the young region, performing flexization. *)
    (* Hash_set.iter region ~f:(fun type_ ->
        match U.Type.get_structure type_ with
        | U.Type.Rigid_var rigid_view ->
          let rigid_var = U.Rigid_view.repr rigid_view in
          if get_level type_ = state.current_level
          then (
            match Hashtbl.find rigid_vars rigid_var with
            | Some dst ->
              (try U.Type.flexize ~src:type_ ~dst with
              | U.Type.Cannot_flexize _ ->
                Caml.Format.printf
                  "Could not flexize since is not rigid variable\n";
                raise (Cannot_flexize rigid_var))
            | None ->
              Caml.Format.printf
                "Could not flexize since rigid var is unbound\n";
              (* raise (Cannot_flexize rigid_var)) *) ())
        | _ -> ()); *)
    (* Iterate through the young region, generalizing variables 
       (or updating their region).  *)
    Hash_set.iter region ~f:(fun type_ ->
        if level type_ < state.current_level
        then set_region state type_
        else
          (* Caml.Format.printf "Generalizing %d\n" (U.Type.id type_); *)
          generalize_type type_);
    (* Iterate through the young region, computing the list
       of generalizable variables. *)
    let generalizable =
      region
      (* Invariant, all nodes in [region] are now generic *)
      |> Hash_set.filter ~f:(fun type_ ->
             is_generic_at type_ state.current_level
             &&
             match former type_ with
             | None -> Hash_set.is_empty (get_rigid_vars type_)
             | _ -> false)
      |> Hash_set.to_list
    in
    (* Clear the young region now *)
    Hash_set.clear region;
    Hashtbl.to_alist rigid_vars_tbl, generalizable


  (* [exit state ~rigid_vars ~types] performs generalization
     of [types], returns the list of generalized variables and schemes.
     
     Ensures [rigid_vars] do not escape. 
  *)
  let exit state ~rigid_vars ~types =
    pp_state state "Before exit";
    (* Detect cycles in roots. *)
    List.iter ~f:U.occurs_check types;
    (* Now update the lazily updated scopes of every node in the young region *)
    update_scopes state;
    (* Now update the lazily updated levels of every node in the young
       region. *)
    update_levels state;
    (* Generalize variables. *)
    let rigid_vars, generalizable = generalize state ~rigid_vars in
    (* Check that rigid variables have no escaped. *)
    (match
       List.find rigid_vars ~f:(fun (_, var) -> level var < state.current_level)
     with
    | None -> ()
    | Some (rigid_var, _) -> raise (Rigid_variable_escape rigid_var));
    (* Helper function for constructing a new type scheme *)
    let make_scheme =
      let level = state.current_level in
      fun root -> { root; level }
    in
    (* Exit the current region *)
    state.current_level <- state.current_level - 1;
    pp_state state "After exit";
    generalizable, List.map ~f:make_scheme types


  type variables = U.Type.t list

  let root { root; _ } = root

  let variables { root; level } =
    (* Hash set records whether we've visited a given 
       graphic type node. Prevents cyclic execution of [loop]. *)
    let visited : U.Type.t Hash_set.t = Hash_set.create (module U.Type) in
    let variables = ref [] in
    let rec loop type_ =
      (* A type [typ] contains a generic variable if it is generic
         w/ level [level]. *)
      if is_generic_at type_ level && not (Hash_set.mem visited type_)
      then (
        (* We mark node visited here to ensure that 
           when we recurse below, we don't reach an infinite loop
           due to cycles in [root]. 
        *)
        Hash_set.add visited type_;
        (* Iterate on non-productives
           TODO: Implement U.Non_productive_view.map *)
        (* U.Non_productive_view.iter (U.Type.get_non_productive_view type_)
          ~f:(Former.iter ~f:loop); *)
        (* Check the structure of the type [typ]. 
           If [Var], add to the relevant quantifier list,
           otherwise recurse.  
        *)
        match former type_ with
        | None -> variables := type_ :: !variables
        | Some former -> Former.iter former ~f:loop)
    in
    loop root;
    !variables


  let mono_scheme type_ =
    (* Determine whether [type_] contains rigid variables, if so, then we also need
       to generalize, for a partial copy. *)
    { root = type_; level = level type_ + 1 }


  (* When instantiating a scheme [scheme], we must traverse it's body, 
     creating new (copied) variables for each generic variable, returning 
     the new root and new variables.
  
     This is equivalent to the theortical notion of a "substitution". 
  *)

  let instantiate state { root; level = level' } =
    (* Caml.Format.printf "Instantiating: %d\n" (U.Type.id root); *)
    (* The [copied] hash table stores a mapping from graphic type nodes 
       to their related copied forms. This ensures only 1 copy per 
       variable. 
    *)
    let copied : (U.Type.t, U.Type.t) Hashtbl.t =
      Hashtbl.create (module U.Type)
    in
    (* We also need to keep track of the instantiated variables,
       using a [instance variables] record. *)
    let instance_variables = ref [] in
    (* We traverse the type, if it is generic, then we copy it
       and recursivly traverse. Otherwise, we return the type 
       as is. 
    *)
    let rec copy type_ =
      (* Caml.Format.printf "Copying %d\n" (U.Type.id type_); *)
      (* We use [is_generic] instead of [is_generic_at],
         since we may have to copy generic variables that
         have been generalized by a different scheme. 
      *)
      if not (is_generic type_)
      then type_
      else (
        (* Caml.Format.printf "%d is generic\n" (U.Type.id type_); *)
        try Hashtbl.find_exn copied type_ with
        | Not_found_s _ ->
          (* We now update the structure according to the original 
             structure of [typ].  *)
          let new_type =
            match former type_ with
            | None ->
              (* The condition [get_level typ = level] now asserts
                 [is_generic_at typ level], hence we need to instantiate
                 the variable, adding it to the instance variables. 
              *)
              let new_type = make_flexible_var state in
              if level type_ = level'
              then instance_variables := new_type :: !instance_variables;
              new_type
            | Some former -> make_former state (Former.map ~f:copy former)
          in
          (* Set the mapping from the original node to the copied 
             node. *)
          Hashtbl.set copied ~key:type_ ~data:new_type;
          new_type)
    in
    (* Copy the root, yielding the instance variables (as a side-effect). *)
    let root = copy root in
    (* Caml.Format.printf "Instantiated result:\n"; *)
    (* pp_type_explicit root; *)
    !instance_variables, root
end
