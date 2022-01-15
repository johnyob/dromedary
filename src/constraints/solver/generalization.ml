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

  module Tag = struct
    (* [t] is the type of tags, encoding the level and whether the node is generic. *)
    type t =
      { mutable level : level
      ; mutable is_generic : bool
      }
    [@@deriving sexp_of]

    exception Cannot_update_generic of t

    (* [merge t1 t2] merges 2 tags, merging their levels. 
       Generic tags cannot be merged, raising [Cannot_update_generic]. *)
    let merge t1 t2 =
      if t1.is_generic then raise (Cannot_update_generic t1);
      if t2.is_generic then raise (Cannot_update_generic t2);
      { level = merge_level t1.level t2.level; is_generic = false }


    (* [set_level t l] sets the level of [t] to [l]. 
       [Cannot_update_generic t] is raised if [t] is generic. *)
    let set_level t level =
      if t.is_generic then raise (Cannot_update_generic t);
      t.level <- level


    (* [get_level t] returns the level of the tag [t]. *)
    let get_level t = t.level

    (* [is_generic t] returns whether t is generic. *)
    let is_generic t = t.is_generic

    (* [generalize t] lifts the tag [t] to a generic tag. *)
    let generalize t = t.is_generic <- true
  end

  module Unifier = Unifier.Make (Former) (Tag)
  module Abbreviations = Unifier.Abbreviations

  (* [U] and [A] are aliases, used for a short prefix below. *)
  module U = Unifier
  module A = Abbreviations

  (* [set_level type_ level] sets the level of the type [type_] to [level]. *)
  let set_level type_ level = Tag.set_level (U.Type.get_metadata type_) level

  (* [get_level type_] returns the level of type [type_]. *)
  let get_level type_ = Tag.get_level (U.Type.get_metadata type_)

  (* [update_level type_ level] is equivalent to [set_level type_ (min (get_level type_) level)]. *)
  let update_level type_ level =
    if level < get_level type_ then set_level type_ level


  (* [is_generic type_] returns whether the current type [type_] is "generic". *)
  let is_generic type_ = Tag.is_generic (U.Type.get_metadata type_)

  (* [is_generic_at type_ level] returns whether the current type [type] is 
     generic and is generalized at level [level]. *)
  let is_generic_at type_ level =
    let tag = U.Type.get_metadata type_ in
    Tag.is_generic tag && Tag.get_level tag = level


  (* [generalize_type type_] generalizes the type [type_]. *)
  let generalize_type type_ = Tag.generalize (U.Type.get_metadata type_)

  (* [make_var_] and [make_former_] are internal functions for making type 
     variables and type formers wrapping [Unifier]. *)

  let make_flexible_var_ level =
    U.Type.make_flexible_var { level; is_generic = false }


  let make_rigid_var_ rigid_var level =
    U.Type.make_rigid_var rigid_var { level; is_generic = false }


  let make_former_ ~ctx former level =
    U.Type.make_former ~ctx former { level; is_generic = false }


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
    ; abbrev_ctx : A.Ctx.t
    }

  (* [make_state ()] makes a new empty state. *)

  let make_state abbrev_ctx =
    { current_level = outermost_level - 1; regions = Vec.make (); abbrev_ctx }


  (* let pp_type_explicit type_ =
    let rec pp_type_explicit type_ =
      match U.Type.get_structure type_ with
      | U.Type.Var { flexibility = _ } ->
        Sexp.Atom (Int.to_string (U.Type.id type_))
      | U.Type.Former productive_view ->
        Former.sexp_of_t
          pp_type_explicit
          (U.Productive_view.repr productive_view)
    in
    Caml.Format.printf "%s\n" (Sexp.to_string_mach (pp_type_explicit type_))


  let pp_type type_ =
    Caml.Format.printf
      "id = %d, level = %d, is_generic = %b"
      (U.Type.id type_)
      (get_level type_)
      (is_generic type_);
    (match U.Type.get_structure type_ with
    | Var { flexibility } ->
      Caml.Format.printf
        ", flexibility = %s"
        (Sexp.to_string_hum (U.Type.sexp_of_flexibility flexibility))
    | _ -> ());
    Caml.Format.printf "\n"


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
    pp_regions state *)

  (* [set_region type_] adds [type_] to it's region (defined by [type_]'s level). *)

  let set_region state type_ =
    (* Stdio.print_string "set_region"; *)
    Hash_set.add (Vec.get_exn state.regions (get_level type_)) type_


  (* [make_var] creates a fresh unification variable, setting it's level
     and region. *)

  let make_flexible_var state =
    let var = make_flexible_var_ state.current_level in
    set_region state var;
    (* Caml.Format.printf "New variable:\n";
    pp_type var; *)
    var


  let make_rigid_var state rigid_var =
    let var = make_rigid_var_ rigid_var state.current_level in
    set_region state var;
    (* Caml.Format.printf "New variable:\n";
      pp_type var; *)
    var


  (* [make_former] creates a fresh unification type node 
     w/ the structure provided by the former [former]. 
      
     It initialize the level to the current level. 
  *)
  let make_former state former =
    let former =
      make_former_ ~ctx:state.abbrev_ctx former state.current_level
    in
    set_region state former;
    (* Caml.Format.printf "New former:\n";
    pp_type former;
    pp_type_explicit former; *)
    former


  let unify state t1 t2 =
    (* Caml.Format.printf "Unify: %d %d\n" (U.Type.id t1) (U.Type.id t2); *)
    U.unify
      ~ctx:state.abbrev_ctx
      ~metadata:(fun () -> { level = state.current_level; is_generic = false })
      t1
      t2


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

  let update_levels state =
    (* We note that levels only decrease (since we take the minimum when merging),
       hence we process nodes in level order. 
       
       This allows us to only visit each node once, providing the invariant that 
       at the current level [level], all nodes visited are of level [<= level]. 
       
       To implement this, we convert the young region into a sorted array
       which we iterate over to begin the traversal. *)
    let is_young = is_young state in
    let young_region = young_region state |> Hash_set.to_array in
    Array.sort young_region ~compare:(fun t1 t2 ->
        Int.compare (get_level t1) (get_level t2));
    (* Caml.Format.printf "Array order:\n"; *)
    (* Caml.Format.printf
      "%s\n"
      (Array.to_list young_region
      |> List.map ~f:(fun t -> Int.to_string (U.Type.id t))
      |> String.concat ~sep:","); *)
    (* Hash set records whether we've visited a given 
       graphic type node. Prevents cyclic execution of [loop]. *)
    let visited : U.Type.t Hash_set.t = Hash_set.create (module U.Type) in
    let rec loop type_ level =
      if not (Hash_set.mem visited type_)
      then (
        (* Mark as visited first. This is required with graphic types
           containing cycles. Allows us to reduce # of occurs checks. *)
        Hash_set.add visited type_;
        (* Regardless of whether a node is young or old, 
          we update it's level. *)
        update_level type_ level;
        (* If a node is old, then we stop traversing (hence the [is_young] check). *)
        if is_young type_
        then (
          (* Visit non-productive view first. We note that there is no need to 
             fold over the view, computing the maximum level of children, since:   
             If the view is non-empty => contains a reference back to [type_] in the view, hence 
             maximum level is [level].
          *)
          U.Non_productive_view.iter
            (U.Type.get_non_productive_view type_)
            ~f:(Former.iter ~f:(fun type_ -> loop type_ level));
          match U.Type.get_structure type_ with
          | U.Type.Flexible_var | U.Type.Rigid_var _ ->
            (* In the variable case, we cannot traverse any further
              and no updates need be performed (since the level update)
              is performed above. 
            *)
            ()
          | U.Type.Former productive_view ->
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
              (U.Productive_view.fold
                 productive_view
                 ~init:outermost_level
                 ~f:(fun former acc ->
                   Former.fold former ~init:acc ~f:(fun type_ acc ->
                       loop type_ level;
                       max (get_level type_) acc)))))
    in
    Array.iter ~f:(fun type_ -> loop type_ (get_level type_)) young_region


  exception Rigid_variable_escape of U.Rigid_var.t
  exception Cannot_flexize of U.Rigid_var.t

  (* [generalize state ~rigid_vars] generalizes variables in the current
     region according to the new levels propagated by [update_levels].
     
     If a node has a level < !current_level, then it belongs in an 
     older region. It is moved using [set_region].
     
     Otherwise, if the node has level = !current_level, then it may 
     be generalized, using [generalize_type]. 
     
     Once generalized, we compute the list of generalizable
     variables. 

     The process of flexization, the conversion of rigid variables to
     generic flexible variables also occurs here.
  *)
  let generalize state ~rigid_vars =
    (* Create a mapping between rigid variables and flexible variables for flexization. *)
    let rigid_vars =
      Hashtbl.of_alist_exn
        (module U.Rigid_var)
        (List.map rigid_vars ~f:(fun rigid_var ->
             rigid_var, make_flexible_var state))
    in
    (* Get the young region, since we will be performing several traversals
       of it. *)
    let region = young_region state in
    (* Iterate through the young region, performing flexization. *)
    Hash_set.iter region ~f:(fun type_ ->
        match U.Type.get_structure type_ with
        | U.Type.Rigid_var rigid_var ->
          (match Hashtbl.find rigid_vars rigid_var with
          | Some dst -> U.Type.flexize ~src:type_ ~dst
          | None -> raise (Cannot_flexize rigid_var))
        | _ -> ());
    (* Iterate through the young region, generalizing variables 
       (or updating their region).  *)
    Hash_set.iter region ~f:(fun type_ ->
        (* assert (not (is_rigid type_)); *)
        if get_level type_ < state.current_level
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
             match U.Type.get_structure type_ with
             | U.Type.Flexible_var -> true
             | U.Type.Rigid_var _ -> assert false
             | U.Type.Former _ -> false)
      |> Hash_set.to_list
    in
    (* Clear the young region now *)
    Hash_set.clear region;
    Hashtbl.to_alist rigid_vars, generalizable


  (* [exit state ~rigid_vars ~types] performs generalization
     of [types], returns the list of generalized variables and schemes.
     
     Ensures [rigid_vars] do not escape. 
  *)
  let exit state ~rigid_vars ~types =
    (* pp_state state "Before exit"; *)
    (* Detect cycles in roots. *)
    List.iter ~f:U.occurs_check types;
    (* Now update the lazily updated levels of every node in the young
       region. *)
    update_levels state;
    (* Generalize variables. *)
    let rigid_vars, generalizable = generalize state ~rigid_vars in
    (* Check that rigid variables have no escaped. *)
    (match
       List.find rigid_vars ~f:(fun (_, var) -> get_level var < state.current_level)
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
    (* pp_state state "After exit"; *)
    generalizable, List.map ~f:make_scheme types


  type variables = U.Type.t list

  let root { root; _ } = root

  (* Usage of abbreviations in type schemes, etc. Abbreviations are dropped in type schemes. 

     This is because the representative is used to avoid additional expansions, and abbreviations
     are typically local.
  *)

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
        (* Check the structure of the type [typ]. 
           If [Var], add to the relevant quantifier list,
           otherwise recurse.  
        *)
        match U.Type.get_structure type_ with
        | U.Type.Flexible_var -> variables := type_ :: !variables
        | U.Type.Rigid_var _ ->
          (* Rigid variables cannot occur as generalized variables in type schemes *)
          assert false
        | U.Type.Former productive_view ->
          U.Productive_view.repr productive_view |> Former.iter ~f:loop)
    in
    loop root;
    !variables


  let mono_scheme type_ = { root = type_; level = get_level type_ + 1 }

  (* When instantiating a scheme [scheme], we must traverse it's body, 
     creating new (copied) variables for each generic variable, returning 
     the new root and new variables.
  
     This is equivalent to the theortical notion of a "substitution". 
  *)

  let instantiate state { root; level } =
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
          let new_type =
            match U.Type.get_structure type_ with
            | U.Type.Rigid_var _ ->
              (* Rigid variables cannot be generic. If they are, then flexization
                has failed! *)
              assert false
            | U.Type.Flexible_var ->
              (* The condition [get_level typ = level] now asserts
                  [is_generic_at typ level], hence we need to instantiate
                  the variable, adding it to the instance variables. 
              *)
              let new_type = make_flexible_var state in
              if get_level type_ = level
              then instance_variables := new_type :: !instance_variables;
              new_type
            | U.Type.Former productive_view ->
              let former =
                U.Productive_view.repr productive_view |> Former.map ~f:copy
              in
              make_former state former
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
