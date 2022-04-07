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

module Make (Label : Comparable.S) (Former : Type_former.S) = struct
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

  module Structure = struct
    (* Instantiate structures *)
    module Abbreviations = Abbreviations (Of_former (Former)) (Former)
    module Ambivalent = Ambivalent (Abbreviations)
    module Rows = Rows (Label) (Ambivalent)
    module First_order = First_order (Rows)

    type 'a t =
      { mutable level : int
      ; mutable is_generic : bool
      ; mutable structure : 'a First_order.t
      }
    [@@deriving sexp_of]

    let map t ~f = { t with structure = First_order.map t.structure ~f }
    let iter t ~f = First_order.iter t.structure ~f
    let fold t ~f ~init = First_order.fold t.structure ~f ~init

    type 'a ctx =
      { equations_ctx : Ambivalent.Equations.Ctx.t
      ; abbrev_ctx : Abbreviations.Abbrev.Ctx.t
      ; make : 'a First_order.t -> 'a
      }

    exception Cannot_merge = First_order.Cannot_merge

    let make_former former : _ First_order.t =
      Structure
        (Structure (Ambivalent.make (Structure (Abbreviations.make former))))


    let make_rigid_var rigid_var : _ First_order.t =
      Structure (Structure (Ambivalent.make (Rigid_var rigid_var)))


    let make_row_uniform type_ : _ First_order.t = Structure (Row_uniform type_)

    let make_row_cons ~label ~field ~tl : _ First_order.t =
      Structure (Row_cons (label, field, tl))


    let make structure level = { is_generic = false; structure; level }

    let to_abbrev_ctx ctx : _ Abbreviations.ctx =
      { abbrev_ctx = ctx.abbrev_ctx
      ; make_structure = (fun structure -> ctx.make (make_former structure))
      ; make_var = (fun () -> ctx.make Var)
      ; super_ = ()
      }


    let to_ambiv_ctx ctx : _ Ambivalent.ctx =
      { equations_ctx = ctx.equations_ctx
      ; make = (fun structure -> ctx.make (Structure (Structure structure)))
      ; super_ = to_abbrev_ctx ctx
      }


    let to_row_ctx ctx : _ Rows.ctx =
      { make_var = (fun () -> ctx.make Var)
      ; make_structure = (fun structure -> ctx.make (Structure structure))
      ; super_ = to_ambiv_ctx ctx
      }


    let merge ~ctx ~equate t1 t2 =
      let level = min t1.level t2.level in
      let is_generic = false in
      let structure =
        First_order.merge
          ~ctx:(to_row_ctx ctx)
          ~equate
          t1.structure
          t2.structure
      in
      { level; is_generic; structure }


    type 'a repr =
      | Flexible_var
      | Row_uniform of 'a
      | Row_cons of Label.t * 'a * 'a
      | Rigid_var of Rigid_var.t
      | Former of 'a Former.t

    let repr structure =
      match structure.structure with
      | Var -> Flexible_var
      | Structure (Row_uniform t) -> Row_uniform t
      | Structure (Row_cons (l, t1, t2)) -> Row_cons (l, t1, t2)
      | Structure (Structure structure) ->
        (match Ambivalent.repr structure with
        | Rigid_var rigid_var -> Rigid_var rigid_var
        | Structure structure -> Former (Abbreviations.repr structure))
  end

  module U = Unifier.Make (Structure)

  let structure type_ = (U.Type.structure type_).structure

  let set_structure type_ structure' =
    let structure = U.Type.structure type_ in
    structure.structure <- structure'


  let level type_ = (U.Type.structure type_).level
  let is_generic type_ = (U.Type.structure type_).is_generic

  let update_level type_ level =
    let structure = U.Type.structure type_ in
    if level < structure.level then structure.level <- level


  let is_generic_at type_ level =
    let structure = U.Type.structure type_ in
    structure.is_generic && structure.level = level


  let generalize_type type_ = (U.Type.structure type_).is_generic <- true

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

  type region = U.Type.t list

  (* State
  
     We have two elements of persistent state in generalization.
     
     The current level (the number of stack frames) and the regions (1 for 
     each current stack frame). Hence the length of regions is bounded by 
     the current level. 

     Invariant: [length regions = current_level + 1]
  *)

  type state =
    { mutable current_level : level
    ; rigid_vars : (Rigid_var.t, U.Type.t list) Hashtbl.t
    ; regions : (region, [ `R | `W ]) Vec.t
    }

  (* [make_state ()] makes a new empty state. *)

  let make_state () =
    { current_level = outermost_level - 1
    ; regions = Vec.make ()
    ; rigid_vars = Hashtbl.create (module Rigid_var)
    }


  open Structure

  (* [set_region type_] adds [type_] to it's region (defined by [type_]'s level). *)
  let set_region state type_ =
    let level = level type_ in
    Vec.set_exn state.regions level (type_ :: Vec.get_exn state.regions level)


  let make ~state structure =
    let new_type = U.Type.make (Structure.make structure state.current_level) in
    set_region state new_type;
    new_type


  module Unifier = struct
    include U

    type ctx =
      { abbrev_ctx : Abbreviations.Abbrev.Ctx.t
      ; equations_ctx : Ambivalent.Equations.Ctx.t
      }

    let empty_ctx =
      { equations_ctx = Ambivalent.Equations.Ctx.empty
      ; abbrev_ctx = Abbreviations.Abbrev.Ctx.empty
      }


    let unify ~state ~ctx t1 t2 =
      Log.debug (fun m -> m "Unify: %d %d.\n" (U.Type.id t1) (U.Type.id t2));
      U.unify
        ~ctx:
          { abbrev_ctx = ctx.abbrev_ctx
          ; equations_ctx = ctx.equations_ctx
          ; make = make ~state
          }
        t1
        t2
  end

  open Unifier

  let outermost_scope = Ambivalent.Equations.Scope.outermost_scope

  module Rigid_type = struct
    include Ambivalent.Rigid_type

    let make_former former = make_structure (Abbreviations.make former)
  end

  module Equations = struct
    include Ambivalent.Equations.Ctx

    let add ~state ~abbrev_ctx t type1 type2 =
      add
        ~ctx:
          { abbrev_ctx
          ; make_structure =
              (fun structure ->
                Ambivalent.Rigid_type.make_structure
                  (Abbreviations.make structure))
          ; make_var = Ambivalent.Rigid_type.make_var
          ; super_ = ()
          }
        t
        type1
        type2
        state.current_level
  end

  module Abbrev_type = struct
    include Abbreviations.Abbrev.Type

    let make_former = make_structure
  end

  module Abbreviations = struct
    module Abbrev = Abbreviations.Abbrev
    include Abbrev.Ctx

    let add t ~abbrev:(abbrev_former, abbrev_type) =
      add t ~abbrev:(Abbrev.make abbrev_former abbrev_type)
  end

  let pp_type_explicit ppf type_ =
    let rec pp_type_explicit type_ =
      U.Type.structure type_ |> Structure.sexp_of_t pp_type_explicit
    in
    Format.fprintf ppf "%s\n" (Sexp.to_string_hum (pp_type_explicit type_))


  let pp_type ppf type_ =
    Format.fprintf
      ppf
      "id = %d, level = %d is_generic = %b\n"
      (U.Type.id type_)
      (level type_)
      (is_generic type_)


  let pp_region ppf i region =
    Format.fprintf ppf "Region %d\n" i;
    List.iter
      ~f:(fun type_ ->
        pp_type ppf type_;
        pp_type_explicit ppf type_)
      region


  let pp_regions ppf state = Vec.iteri (pp_region ppf) state.regions

  let pp_current_level ppf state =
    Format.fprintf ppf "Current level: %d\n" state.current_level


  let pp_state ppf state =
    pp_current_level ppf state;
    pp_regions ppf state


  (* [make_flexible_var] creates a fresh unification variable, setting it's level
     and region. *)

  let make_flexible_var ~state =
    let var = make ~state Var in
    Log.debug (fun m -> m "New variable:\n %a" pp_type var);
    var


  let make_rigid_var ~state rigid_var =
    let var = make ~state (make_rigid_var rigid_var) in
    Log.debug (fun m ->
        m "New rigid variable: %d.\n %a" (rigid_var :> int) pp_type var);
    var


  (* [make_former] creates a fresh unification type node 
     w/ the structure provided by the former [former]. 
      
     It initialize the level to the current level. 
  *)
  let make_former ~state former =
    let former = make ~state (make_former former) in
    Log.debug (fun m -> m "New former:\n %a" pp_type former);
    former


  let make_row_uniform ~state type_ =
    let row_uniform = make ~state (make_row_uniform type_) in
    Log.debug (fun m -> m "New row uniform:\n %a" pp_type row_uniform);
    row_uniform


  let make_row_cons ~state ~label ~field ~tl =
    let row_cons = make ~state (make_row_cons ~label ~field ~tl) in
    Log.debug (fun m -> m "New row cons:\n %a" pp_type row_cons);
    row_cons


  let flexize ~state src dst =
    Log.debug (fun m ->
        m "Flexize: %d -> %d.\n" (U.Type.id src) (U.Type.id dst));
    set_structure src Var;
    unify ~state ~ctx:empty_ctx src dst


  (* [enter ()] creates a new stack frame and enter it. *)

  let enter ~state =
    state.current_level <- state.current_level + 1;
    Log.debug (fun m -> m "Entering level: %d.\n" state.current_level);
    Log.debug (fun m -> m "State:\n%a" pp_state state);
    Vec.push [] state.regions


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

  type young_region =
    { region : Type.t list (* A list of all types in the young region. *)
    ; by_level : Type.t array
          (* An array of all types in the young region -- ordered by 
             level (lowest to highest) *)
    ; by_scope : Type.t array
          (* An array of all types in the young region -- ordered by
             scope (highest to lowest) *)
    ; is_young : Type.t -> bool
          (* [is_young] returns whether a type satisfies 
             [level type = state.current_level] *)
    }

  (* Region management
  
     When performing region updates, we often only care about maintaing
     and update nodes within the "young" region (the current region),
     leaving updates in older regions to later phases of generalization.
     
     This notion of region corresponds to Oleg's update queue, however, 
     we split this queue into regions (so we don't need to traverse the
     entire queue when updating).
  *)

  let scope t =
    match structure t with
    | Structure (Structure structure) -> Ambivalent.scope structure
    | _ -> outermost_scope


  (* [young_region state] returns the [young_region] encoding of [state] *)

  let young_region ~state : young_region =
    let region = Vec.get_exn state.regions state.current_level in
    let region_arr = Array.of_list region in
    let by_level =
      Array.sorted_copy region_arr ~compare:(fun t1 t2 ->
          Int.compare (level t1) (level t2))
    in
    let by_scope =
      Array.sorted_copy region_arr ~compare:(fun t1 t2 ->
          -Int.compare (scope t1) (scope t2))
    in
    let is_young =
      let set =
        Hash_set.of_list (module Int) (region |> List.map ~f:U.Type.id)
      in
      fun type_ -> Hash_set.mem set (U.Type.id type_)
    in
    { region; by_level; by_scope; is_young }


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

  let[@landmark] update_scopes young_region =
    Log.debug (fun m -> m "Updating scopes.\n");
    let update_scope t scope =
      match structure t with
      | Structure (Structure structure) ->
        Ambivalent.update_scope structure scope
      | _ -> ()
    in
    (* Hash set records whether we've visited a given 
       graphic type node. Prevents cyclic execution of [loop]. *)
    let visited : U.Type.t Hash_set.t = Hash_set.create (module U.Type) in
    let rec loop type_ scope1 =
      if not (Hash_set.mem visited type_)
      then (
        Log.debug (fun m -> m "Visiting %d.\n" (U.Type.id type_));
        Hash_set.add visited type_;
        Log.debug (fun m -> m "Updating scope to %d.\n" scope1);
        update_scope type_ scope1;
        if young_region.is_young type_
        then
          update_scope
            type_
            (U.Type.structure type_
            |> Structure.fold
                 ~init:Ambivalent.Equations.Scope.outermost_scope
                 ~f:(fun type_ scope2 ->
                   loop type_ scope1;
                   Ambivalent.Equations.Scope.max (scope type_) scope2)))
    in
    List.iter ~f:(fun type_ -> loop type_ (scope type_)) young_region.region;
    Log.debug (fun m -> m "Finished updating scopes.")


  exception Scope_escape of U.Type.t

  let[@landmark] update_levels young_region =
    Log.debug (fun m -> m "Updating levels.\n");
    (* We note that levels only decrease (since we take the minimum when merging),
       hence we process nodes in level order. 
       
       This allows us to only visit each node once, providing the invariant that 
       at the current level [level], all nodes visited are of level [<= level]. 
       
       To implement this, we convert the young region into a sorted array
       which we iterate over to begin the traversal. *)
    (* Hash set records whether we've visited a given graphic type node. 
       Prevents cyclic execution of [loop]. *)
    let visited : U.Type.t Hash_set.t = Hash_set.create (module U.Type) in
    let rec loop type_ level' =
      if not (Hash_set.mem visited type_)
      then (
        Log.debug (fun m -> m "Visiting %d.\n" (U.Type.id type_));
        (* Mark as visited first. This is required with graphic types
           containing cycles. Allows us to reduce # of occurs checks. *)
        Hash_set.add visited type_;
        (* Regardless of whether a node is young or old, 
          we update it's level. *)
        update_level type_ level';
        Log.debug (fun m -> m "Updating level w/ %d.\n" level');
        (* If a node is old, then we stop traversing (hence the [is_young] check). *)
        if young_region.is_young type_
        then
          (* If the node is a type former, then we need to traverse it's 
            children and determine it's correct level.
            
            Levels must satisfy the following monotonicty condition:
            level type <= k => get_type type' <= k where type' is a 
            child of type. 
          *)
          U.Type.structure type_
          |> Structure.iter ~f:(fun type_ -> loop type_ level'))
    in
    List.iter ~f:(fun type_ -> loop type_ (level type_)) young_region.region


  let[@landmark] scope_check young_region =
    List.iter young_region.region ~f:(fun type_ ->
        match structure type_ with
        | Structure (Structure structure) ->
          let scope = Ambivalent.scope structure in
          if level type_ < scope
          then (
            Log.debug (fun m ->
                m
                  "Scope escape: id=%d, level=%d, scope=%d\n"
                  (U.Type.id type_)
                  (level type_)
                  scope);
            raise (Scope_escape type_))
        | _ -> ())


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

     The process of flexization, the conversion of rigid variables to
     generic flexible variables also occurs here.
  *)
  let[@landmark] generalize ~state young_region =
    (* Iterate through the young region, generalizing variables (or updating their region), 
       adding rigid variables to flexization queue.  *)
    List.iter young_region.region ~f:(fun type_ ->
        if level type_ < state.current_level
        then set_region state type_
        else generalize_type type_;
        match structure type_ with
        | Structure (Structure structure) ->
          (match Ambivalent.repr structure with
          | Rigid_var rigid_var ->
            Hashtbl.update state.rigid_vars rigid_var ~f:(function
                | None -> [ type_ ]
                | Some types -> type_ :: types)
          | _ -> ())
        | _ -> ());
    (* Iterate through the young region, computing the list
       of generalizable variables. *)
    let generalizable =
      List.filter young_region.region ~f:(fun type_ ->
          is_generic_at type_ state.current_level
          &&
          match structure type_ with
          | Var -> true
          | _ -> false)
    in
    generalizable


  (* [exit state ~rigid_vars ~types] performs generalization
     of [types], returns the list of generalized variables and schemes.
     
     Ensures [rigid_vars] do not escape. 
  *)
  let exit ~state ~rigid_vars ~types =
    Log.debug (fun m -> m "Exiting level: %d\n" state.current_level);
    Log.debug (fun m -> m "State before exit:\n%a" pp_state state);
    let young_region = young_region ~state in
    (* Now update the lazily updated scopes of every node in the young region *)
    update_scopes young_region;
    (* Now update the lazily updated levels of every node in the young
       region. *)
    update_levels young_region;
    (* Now perform the scope check *)
    scope_check young_region;
    (* Generalize variables. *)
    let generalizable = generalize ~state young_region in
    (* Flexize the variable *)
    let rigid_vars =
      List.map rigid_vars ~f:(fun rigid_var ->
          let var = make_flexible_var ~state in
          (match Hashtbl.find state.rigid_vars rigid_var with
          | Some rigid_vars ->
            List.iter rigid_vars ~f:(fun x -> flexize ~state x var);
            Hashtbl.remove state.rigid_vars rigid_var
          | None -> ());
          generalize_type var;
          var)
    in
    (* Helper function for constructing a new type scheme *)
    let make_scheme =
      let level = state.current_level in
      fun root -> { root; level }
    in
    (* Clear the young region now *)
    Vec.set_exn state.regions state.current_level [];
    (* Exit the current region *)
    state.current_level <- state.current_level - 1;
    Log.debug (fun m -> m "State after exit:\n%a" pp_state state);
    rigid_vars @ generalizable, List.map ~f:make_scheme types


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
        match structure type_ with
        | Var -> variables := type_ :: !variables
        | Structure structure -> Rows.iter ~f:loop structure)
    in
    loop root;
    !variables


  let mono_scheme type_ = { root = type_; level = level type_ + 1 }

  (* When instantiating a scheme [scheme], we must traverse it's body, 
     creating new (copied) variables for each generic variable, returning 
     the new root and new variables.
  
     This is equivalent to the theortical notion of a "substitution". 
  *)

  let instantiate ~state { root; level = level' } =
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
      let open Structure in
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
          let new_type = make_flexible_var ~state in
          Hashtbl.set copied ~key:type_ ~data:new_type;
          (match structure type_ with
          | Var ->
            if level type_ = level'
            then instance_variables := new_type :: !instance_variables
          | Structure (Row_uniform type_) ->
            set_structure new_type (make_row_uniform (copy type_))
          | Structure (Row_cons (l, type1, type2)) ->
            set_structure
              new_type
              (make_row_cons ~label:l ~field:(copy type1) ~tl:(copy type2))
          | Structure (Structure structure) ->
            (match Ambivalent.repr structure with
            | Rigid_var rigid_var ->
              set_structure new_type (make_rigid_var rigid_var)
            | Structure structure ->
              set_structure
                new_type
                (make_former
                   (Former.map ~f:copy (Abbreviations.repr structure)))));
          new_type)
    in
    (* Copy the root, yielding the instance variables (as a side-effect). *)
    let root = copy root in
    !instance_variables, root
end
