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

module Make (Former : Type_former.S) (Metadata : Metadata) :
  S with type 'a former := 'a Former.t and type metadata := Metadata.t = struct
  (* Unification involves unification types, using the union-find 
     data structure. 
     
     These are referred to as "graphical types" in the dissertation. 
     
     While are formalization doesn't exactly match our implementation, 
     the notion provides useful insight. 
  *)

  module Rigid_var = struct
    type t = { id : int } [@@deriving sexp_of]

    let make () = { id = 0 }
    let compare t1 t2 = Int.compare t1.id t2.id
    let hash t = t.id
  end

  module Rigid_path = struct
    type t = Rigid_var.t [@@deriving sexp_of]

    let make a = assert false
    let dot t i = assert false
    let rec compare t1 t2 = assert false
    (* match t1, t2 with
      | Rigid_var a1, Rigid_var a2 -> Int.compare (id a1) (id a2)
      | Rigid_dot (t1, i1), Rigid_dot (t2, i2) ->
        let result = compare t1 t2 in
        if result <> 0 then result else Int.compare i1 i2
      | Rigid_var _, Rigid_dot _ -> -1
      | Rigid_dot _, Rigid_var _ -> 1 *)

    let hash t = assert false
  end

  module Type = struct
    (* A graphical type consists of a [Union_find] node,
       allowing reasoning w/ multi-equations of nodes. *)

    type t = desc Union_find.t [@@deriving sexp_of]

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
      ; mutable structure : structure
      ; mutable ambivalence : ambivalence
      ; mutable metadata : Metadata.t
      }

    (* Graphical type node structures are either variables or type
        formers. 
        
        A variable denotes it's flexibility, using {!flexibility}.
        This is required for unification under a mixed prefix. 
      *)
    and structure =
      | Var
      | Former of t Former.t

    and ambivalence = Rigid_path.t Hash_set.t

    (* [id t] returns the unique identifier of the type [t]. *)
    let id t = (Union_find.find t).id

    (* [get_structure t] returns the structure of [t]. *)
    let get_structure t = (Union_find.find t).structure

    (* [set_structure t structure] sets the structure of [t] to [structure]. *)
    let set_structure t structure = (Union_find.find t).structure <- structure
    let get_ambivalence t = (Union_find.find t).ambivalence

    let set_ambivalence t ambivalence =
      (Union_find.find t).ambivalence <- ambivalence


    (* [get_metadata t] returns the metadata of [t]. *)
    let get_metadata t = (Union_find.find t).metadata

    (* [set_metadata t metadata] sets the metadata of [t] to [metadata]. *)
    let set_metadata t metadata = (Union_find.find t).metadata <- metadata

    (* [compare t1 t2] computes the ordering of [t1, t2],
       based on their unique identifiers. *)

    let compare t1 t2 = Int.compare (id t1) (id t2)

    (* [hash t] computes the hash of the graphical type [t]. 
       Based on it's integer field: id. *)

    let hash t = Hashtbl.hash (id t)

    module To_dot = struct
      type state =
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
        | Var -> [%string "var"]
        | Former former ->
          Former.sexp_of_t (fun _ -> Atom "") former |> Sexp.to_string_hum


      let metadata_to_string metadata : string =
        metadata |> Metadata.sexp_of_t |> Sexp.to_string_hum


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
            | Var -> ()
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
  end

  open Type

  (* See: https://github.com/janestreet/base/issues/121 *)
  let post_incr r =
    let result = !r in
    Int.incr r;
    result


  (* [make structure metadata] returns a fresh type w/ structure [structure] and
     metadata [metadata]. *)
  let make =
    let id = ref 0 in
    fun structure ambivalence metadata ->
      Union_find.make { id = post_incr id; structure; ambivalence; metadata }


  (* [make_var flexibility metadata] returns a fresh variable 
     with flexibility [flexibility], and metadata [metadata]. *)
  let make_var ambivalence metadata = make Var ambivalence metadata

  (* [make_former former metadata] returns a fresh type former
     with metadata [metadata]. *)
  let make_former former ambivalence metadata =
    make (Former former) ambivalence metadata


  (* [unify_exn] unifies two graphical types. No exception handling is 
     performed here. This is an internal function.
     
     Possible exceptions include:
     - [Former.Iter2], raised when executing Former.iter2 in {unify_form}.

     See {!unify}. 
  *)

  let rec unify_exn = Union_find.union ~f:unify_desc

  (* [unify_desc desc1 desc2] unifies the descriptors of the graph types
     (of multi-equations). *)

  and unify_desc desc1 desc2 =
    { id = desc1.id
    ; structure = unify_structure desc1.structure desc2.structure
    ; metadata = Metadata.merge desc1.metadata desc2.metadata
    ; ambivalence = Hash_set.union desc1.ambivalence desc2.ambivalence
    }


  (* [unify_structure structure1 structure2] unifies two graph type node
     structures. We handle rigid variables here. *)

  and unify_structure structure1 structure2 =
    match structure1, structure2 with
    (* Unification of variables (leaves) and type formers (internal nodes)
    
       We may unify a flexible variable with a type former, yielding
       the same type former. 

       Note that no propagation of metadata is performed. This is required
       by external modules. See {!generalization.ml}. 
    *)
    | Var, structure
    | structure, Var -> structure
    (* Unification between type formers 
    
       We may unify type formers recursively. See {!unify_former}. 
    *)
    | Former former1, Former former2 -> Former (unify_former former1 former2)


  (* [unify_former former1 former2] recursively unifies 2 type formers.

     Here we use our internal unification function [unify_exn],
     to allow exception propagation to the top-level call. *)

  and unify_former former1 former2 =
    Former.iter2_exn ~f:unify_exn former1 former2;
    former1


  exception Unify of Type.t * Type.t

  let unify t1 t2 =
    try unify_exn t1 t2 with
    | Former.Iter2 -> raise (Unify (t1, t2))


  exception Cycle of Type.t

  (* [occurs_check t] detects whether there is a cycle in 
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
        | Var ->
          (* A variable is a leaf. Hence no traversal is
             required, so simply mark as visited. *)
          Hashtbl.set table ~key:t ~data:true
        | Former former ->
          (* Mark this node as grey. *)
          Hashtbl.set table ~key:t ~data:false;
          (* Visit children *)
          Former.iter ~f:loop former;
          (* Mark this variable as black. *)
          Hashtbl.set table ~key:t ~data:true)
    in
    loop


  (* [fold_acyclic type_ ~var ~form] will perform a bottom-up fold
     over the (assumed) acyclic graph defined by the type [type_]. *)

  let fold_acyclic
      (type a)
      type_
      ~(var : Type.t -> a)
      ~(former : a Former.t -> a)
      : a
    =
    (* Hash table records whether node has been visited, and 
      it's computed value. *)
    let visited : (Type.t, a) Hashtbl.t = Hashtbl.create (module Type) in
    (* Recursive loop, folding over the graph *)
    let rec loop type_ =
      try Hashtbl.find_exn visited type_ with
      | Not_found_s _ ->
        let result =
          match get_structure type_ with
          | Var -> var type_
          | Former former' -> former (Former.map ~f:loop former')
        in
        (* We assume we can set [type_] in [visited] *after* traversing
          it's children, since the graph is acyclic. *)
        Hashtbl.set visited ~key:type_ ~data:result;
        result
    in
    loop type_


  let fold_cyclic
      (type a)
      type_
      ~(var : Type.t -> a)
      ~(former : a Former.t -> a)
      ~(mu : Type.t -> a -> a)
      : a
    =
    (* Hash table records the variables that are grey ([false])
       or black ([true]). *)
    let table = Hashtbl.create (module Type) in
    (* Recursive loop that traverses the graph. *)
    let rec loop t =
      match get_structure t with
      | Var ->
        Hashtbl.set table ~key:t ~data:true;
        var t
      | Former former' ->
        if Hashtbl.mem table t
        then (
          (* Mark this node as black *)
          Hashtbl.set table ~key:t ~data:true;
          var t)
        else (
          (* Mark this node as grey. *)
          Hashtbl.set table ~key:t ~data:false;
          (* Visit children *)
          let result = former (Former.map ~f:loop former') in
          let status = Hashtbl.find_exn table t in
          Hashtbl.remove table t;
          if status then mu t result else result)
    in
    loop type_
end
