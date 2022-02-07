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

module Make (Structure : Structure.S) = struct
  (* Unification involves unification types, using the union-find 
     data structure. 
     
     These are referred to as "graphical types" in the dissertation. 
     
     While are formalization doesn't exactly match our implementation, 
     the notion provides useful insight. 
  *)

  type 'a metadata = 'a Structure.Metadata.t [@@deriving sexp_of]
  type 'a structure = 'a Structure.t [@@deriving sexp_of]
  type ctx = Structure.ctx
  type 'a expansive = 'a Structure.expansive

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
      ; mutable metadata : t metadata
      ; mutable structure : t structure
      }
    [@@deriving sexp_of]

    let desc t = Union_find.find t

    (* [id t] returns the unique identifier of the type [t]. *)
    let id t = (desc t).id

    (* [get_structure t] returns the structure of [t]. *)
    let get_structure t = (desc t).structure

    (* [set_structure t structure] sets the structure of [t] to [structure]. *)
    let set_structure t structure =
      let desc = desc t in
      Union_find.set t { desc with structure }


    let get_metadata t = (desc t).metadata

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
        Union_find.make { id = post_incr id; metadata; structure }


    module To_dot = struct
      type 'a state =
        { mutable id : int
        ; buffer : Buffer.t
        }

      let basic_shape ~label () : string =
        let label = String.escaped label in
        [%string {|[style=filled, shape = oval, label = "%{label}"];|}]


      let structure_to_string structure : string =
        Structure.sexp_of_t (fun _ -> Atom "") structure
        |> Sexp.to_string_hum


      let register state t : string =
        let id = [%string "%{state.id#Int}"] in
        Buffer.add_string state.buffer id;
        Buffer.add_char state.buffer ' ';
        Buffer.add_string
          state.buffer
          (basic_shape ~label:(structure_to_string (get_structure t)) ());
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
            get_structure t
            |> Structure.iter ~f:(fun t ->
                   let from = loop t in
                   arrow state ~from ~to_:me);
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

  (* [unify_exn] unifies two graphical types. No exception handling is 
     performed here. This is an internal function.
     
     Possible exceptions include:
     - [Former.Iter2], raised when executing Former.iter2 in {unify_form}.
     - [Clash], raised when incorrectly unifying a rigid variable.

     See {!unify}. 
  *)
  let rec unify_exn ~expansive ~ctx t1 t2 =
    Union_find.union ~f:(unify_desc ~expansive ~ctx) t1 t2


  (* [unify_desc desc1 desc2] unifies the descriptors of the graph types
     (of multi-equations). *)
  and unify_desc ~expansive ~ctx desc1 desc2 =
    let structure =
      unify_structure
        ~expansive
        ~ctx
        (desc1.structure, desc1.metadata)
        (desc2.structure, desc2.metadata)
    in
    let metadata = Structure.Metadata.merge desc1.metadata desc2.metadata in
    { id = desc1.id; structure; metadata }


  (* [unify_structure structure1 structure2] unifies two graph type node
     structures. We handle rigid variables here. *)
  and unify_structure ~expansive =
    let merge = Structure.merge ~expansive in
    fun ~ctx structure1 structure2 ->
      merge ~ctx ~equate:(unify_exn ~expansive ~ctx) structure1 structure2


  exception Unify of Type.t * Type.t

  let unify ~expansive ~ctx t1 t2 =
    try unify_exn ~expansive ~ctx t1 t2 with
    | Structure.Cannot_merge -> raise (Unify (t1, t2))


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
    let rec loop type_ =
      try
        (* We raise an exception [Not_found_s] instead of using
           an option, since it is more efficient.
        *)
        let visited = Hashtbl.find_exn table type_ in
        (* A cycle has occurred is the variable is grey. *)
        if not visited then raise (Cycle type_)
      with
      | Not_found_s _ ->
        Hashtbl.set table ~key:type_ ~data:false;
        (* Visit children *)
        Structure.iter ~f:loop (get_structure type_);
        (* Mark this variable as black. *)
        Hashtbl.set table ~key:type_ ~data:true
    in
    loop


  (* [fold_acyclic type_ ~var ~form] will perform a bottom-up fold
     over the (assumed) acyclic graph defined by the type [type_]. *)

  let fold_acyclic (type a) type_ ~(f : Type.t -> a Structure.t -> a)
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
          f type_ (get_structure type_ |> Structure.map ~f:loop)
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
      ~(f : Type.t -> a Structure.t -> a)
      ~(var : Type.t -> a)
      ~(mu : Type.t -> a -> a)
      : a
    =
    (* Hash table records the variables that are grey ([false])
       or black ([true]). *)
    let table = Hashtbl.create (module Type) in
    (* Recursive loop that traverses the graph. *)
    let rec loop type_ =
      if Hashtbl.mem table type_
      then (
        (* Mark this node as black *)
        Hashtbl.set table ~key:type_ ~data:true;
        var type_)
      else (
        (* Mark this node as grey. *)
        Hashtbl.set table ~key:type_ ~data:false;
        (* Visit children *)
        let result =
          f type_ (get_structure type_ |> Structure.map ~f:loop)
        in
        let status = Hashtbl.find_exn table type_ in
        Hashtbl.remove table type_;
        if status then mu type_ result else result)
    in
    loop type_
end
