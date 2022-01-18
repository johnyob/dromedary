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

(* This module implements a the unifier. *)

open! Import

(* Include module types and type definitions from the [_intf] file. *)

include Unifier_intf

module Make (Former : Former) (Metadata : Metadata.S1) = struct
  (* Unification involves unification types, using the union-find 
     data structure. 
     
     These are referred to as "graphical types" in the dissertation. 
     
     While are formalization doesn't exactly match our implementation, 
     the notion provides useful insight. 
  *)

  module Rigid_var = struct
    type t = int [@@deriving compare, sexp_of]

    let make =
      let next = ref 0 in
      fun () -> post_incr next


    let id t = t
    let hash t = t
  end

  module Type = struct
    (* A graphical type consists of a [Union_find] node,
     allowing reasoning w/ multi-equations of nodes. *)

    type t = desc Union_find.t [@@deriving sexp_of]
    and metadata = t Metadata.t

    (* Graphical type node descriptors contain information related to the 
      node that dominates the multi-equation.

      Each node contains a global unique identifier [id]. 
      This is allocated on [fresh]. On [union], an arbitrary 
      identifier is used from the 2 arguments. 
      
      We use this identifier [id] for a total ordering on nodes, often 
      used for efficient datastructures such as [Hashtbl] or [Hash_set]. 

      Each descriptor stores the node structure [structure].
      It is either a variable or a type former (with graph type node 
      children). 
      
      Each node also maintains some mutable metadata [metadata], whose
      purpose is not related to unification. 
      
      Note: the only operation performed by the unifier wrt metadata is
      the merging of metadata on unification. No further traversals / updates
      are implemented here. 
    *)
    and desc =
      { id : int
      ; structure : structure
      ; metadata : metadata
      }
    [@@deriving sexp_of]

    (* Graphical type node structures are either variables or type
      formers. 
      
      A variable denotes it's flexibility, using {!flexibility}.
      This is required for unification under a mixed prefix. 
    *)
    and structure =
      | Flexible_var
      | Rigid_var of Rigid_var.t
      | Former of t Former.t
    [@@deriving sexp_of]

    (* [desc t] returns the descriptor of [t] *)
    let desc t = Union_find.find t

    (* [id t] returns the unique identifier of the type [t]. *)
    let id t = (desc t).id

    (* [get_structure t] returns the structure of [t]. *)
    let get_structure t = (desc t).structure

    (* [set_structure t structure] sets the structure of [t] to [structure]. *)
    let set_structure t structure =
      let desc = desc t in
      Union_find.set t { desc with structure }


    (* [get_metadata t] returns the metadata of [t]. *)
    let get_metadata t = (desc t).metadata

    (* [set_metadata t metadata] sets the metadata of [t] to [metadata]. *)
    let set_metadata t metadata =
      let desc = desc t in
      Union_find.set t { desc with metadata }


    (* [compare t1 t2] computes the ordering of [t1, t2],
     based on their unique identifiers. *)

    let compare t1 t2 = Int.compare (id t1) (id t2)

    (* [hash t] computes the hash of the graphical type [t]. 
       Based on it's integer field: id. *)

    let hash t = Hashtbl.hash (id t)

    (* [make structure metadata] returns a fresh type w/ structure [structure] and
        metadata [metadata]. *)
    let make =
      let id = ref 0 in
      fun structure metadata ->
        Union_find.make { id = post_incr id; structure; metadata }


    let make_flexible_var metadata = make Flexible_var metadata
    let make_rigid_var rigid_var metadata = make (Rigid_var rigid_var) metadata
    let make_former former metadata = make (Former former) metadata

    module To_dot = struct
      type 'a state =
        { mutable id : int
        ; buffer : Buffer.t
        }

      let basic_shape ~label ~metadata () : string =
        let label = String.escaped label in
        let metadata = String.escaped metadata in
        [%string
          {|[style=filled, tooltip = "%{metadata}", shape = oval, label = "%{label}"];|}]


      let structure_to_string structure : string =
        match structure with
        | Flexible_var -> [%string "*"]
        | Rigid_var rigid_var -> Sexp.to_string (Rigid_var.sexp_of_t rigid_var)
        | Former former ->
          Former.sexp_of_t (fun _ -> Atom "") former |> Sexp.to_string_hum


      let metadata_to_string metadata : string =
        Metadata.sexp_of_t sexp_of_t metadata |> Sexp.to_string_hum


      let register state t : string =
        let id = [%string "%{state.id#Int}"] in
        Buffer.add_string state.buffer id;
        Buffer.add_char state.buffer ' ';
        Buffer.add_string
          state.buffer
          (basic_shape
             ~label:(structure_to_string (get_structure t))
             ~metadata:(metadata_to_string (get_metadata t))
             ());
        Buffer.add_char state.buffer '\n';
        state.id <- state.id + 1;
        id


      let arrow state ~from ~to_ =
        Buffer.add_string state.buffer [%string "%{from} -> %{to_};\n"]


      let follow_type state t =
        let table = Hashtbl.create (module Int) in
        let rec loop t =
          match Hashtbl.find table (id t) with
          | Some me -> me
          | None ->
            let me = register state t in
            Hashtbl.set table ~key:(id t) ~data:me;
            (match get_structure t with
            | Flexible_var | Rigid_var _ -> ()
            | Former former ->
              Former.iter former ~f:(fun t ->
                  let from = loop t in
                  arrow state ~from ~to_:me));
            me
        in
        loop t
    end

    let to_dot t =
      let open To_dot in
      let state = { id = 0; buffer = Buffer.create 2042 } in
      let _root = follow_type state t in
      let contents = Buffer.contents state.buffer in
      [%string "digraph {\n %{contents}}"]


    exception Cannot_flexize of t

    let flexize_desc desc_src desc_dst =
      { id = desc_dst.id
      ; structure = desc_dst.structure
      ; metadata = Metadata.merge desc_src.metadata desc_dst.metadata
      }


    let flexize ~src ~dst =
      match get_structure src with
      | Rigid_var _ -> Union_find.union src dst ~f:flexize_desc
      | _ -> raise (Cannot_flexize src)
  end

  open Type

  exception Cannot_unify_rigid_variable

  (* [unify_exn] unifies two graphical types. No exception handling is 
     performed here. This is an internal function.
     
     Possible exceptions include:
     - [Former.Iter2], raised when executing Former.iter2 in {unify_former}.

     See {!unify}. 
  *)

  let rec unify_exn ~ctx t1 t2 = Union_find.union t1 t2 ~f:(unify_desc ~ctx)

  and unify_desc ~ctx desc1 desc2 =
    { id = desc1.id
    ; structure = unify_structure ~ctx desc1.structure desc2.structure
    ; metadata = Metadata.merge desc1.metadata desc2.metadata
    }


  (* [unify_structure structure1 structure2] unifies two graph type node
     structures. We handle rigid variables here. *)

  and unify_structure ~ctx structure1 structure2 =
    match structure1, structure2 with
    (* Unification of variables
    
       Unification is permitted between distinct variables only if 
       both variables are *not* rigid.
  
       In the case of 2 rigid variable, we raise [Cannot_unify_rigid_variable].
       We may unify a rigid variable with itself. However, this case does 
       not arise here since [Union_find.union] checks physical equality 
       before before [unify_structure] is executed. 
    *)
    | Rigid_var rigid_var1, Rigid_var rigid_var2 ->
      if Rigid_var.compare rigid_var1 rigid_var2 = 0
      then Rigid_var rigid_var1
      else raise Cannot_unify_rigid_variable
    | Rigid_var rigid_var, Flexible_var | Flexible_var, Rigid_var rigid_var ->
      Rigid_var rigid_var
    | Flexible_var, Flexible_var -> Flexible_var
    (* Unification of variables (leaves) and type formers (internal nodes)
    
       We may unify a flexible variable with a type former, yielding
       the same type former. 
       Note that no propagation of metadata is performed. This is required
       by external modules. See {!generalization.ml}. 
    *)
    | Flexible_var, Former former | Former former, Flexible_var -> Former former
    (* Unification between a rigid variable and a type former is not 
       permitted. We raise [Unify_rigid]. *)
    | Rigid_var _, Former _ | Former _, Rigid_var _ ->
      raise Cannot_unify_rigid_variable
    (* Unification between type formers 
    
       We may unify type formers recursively. See {!unify_former}. 
    *)
    | Former productive_view1, Former productive_view2 ->
      Former (unify_former ~ctx productive_view1 productive_view2)


  (* [unify_former former1 former2] recursively unifies 2 type formers.

     Here we use our internal unification function [unify_exn],
     to allow exception propagation to the top-level call. *)

  and unify_former ~ctx former1 former2 =
    Former.iter2_exn ~ctx former1 former2 ~f:(unify_exn ~ctx);
    former1


  exception Unify of Type.t * Type.t

  let unify ~ctx t1 t2 =
    try unify_exn ~ctx t1 t2 with
    | Former.Iter2 | Cannot_unify_rigid_variable -> raise (Unify (t1, t2))


  exception Cycle of Type.t

  (* [occurs_check ~ctx t] detects whether there is a cycle in 
     the graphical type [t]. 
      
     If a cycle is detected, [Cycle t] is raised. 
  *)
  let occurs_check =
    (* Hash table records the variables that are grey ([false])
       or black ([true]). *)
    let table = Hashtbl.create (module Type) in
    (* Recursive loop that traverses the graph, checking 
       for cycles. *)
    let rec loop t =
      try
        (* We raise an exception [Not_found_s] instead of using
           an option, since it is more efficient.
        *)
        let visited = Hashtbl.find_exn table t in
        (* A cycle has occurred is the variable is grey. *)
        if not visited then raise (Cycle t)
      with
      | Not_found_s _ ->
        (match get_structure t with
        | Flexible_var | Rigid_var _ ->
          (* A variable is a leaf. Hence no traversal is
             required, so simply mark as visited. *)
          Hashtbl.set table ~key:t ~data:true
        | Former former ->
          (* Mark this node as grey. *)
          Hashtbl.set table ~key:t ~data:false;
          (* Visit children *)
          Former.iter former ~f:loop;
          (* Mark this variable as black. *)
          Hashtbl.set table ~key:t ~data:true)
    in
    loop
end
