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

  type 'a structure = 'a Structure.t [@@deriving sexp_of]
  type 'a ctx = 'a Structure.ctx

  module Type = struct
    module T = struct
      (* A graphical type consists of a [Union_find] node,
     allowing reasoning w/ multi-equations of nodes. *)

      type t = desc Union_find.t

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
        ; mutable structure : t structure
        }

      let desc t = Union_find.get t

      let rec sexp_of_desc { id; structure } =
        [%sexp Id (id : int), Structure (structure : t structure)]


      and sexp_of_t t = t |> desc |> sexp_of_desc

      (* [id t] returns the unique identifier of the type [t]. *)
      let id t = (desc t).id

      (* [structure t] returns the structure of [t]. *)
      let structure t = (desc t).structure

      (* [set_structure t structure] sets the structure of [t] to [structure]. *)
      let set_structure t structure =
        let desc = desc t in
        Union_find.set t { desc with structure }


      (* [compare t1 t2] computes the ordering of [t1, t2],
       based on their unique identifiers. *)

      let compare t1 t2 = Int.compare (id t1) (id t2)

      (* [hash t] computes the hash of the graphical type [t]. 
       Based on it's integer field: id. *)

      let hash t = Hashtbl.hash (id t)
      let sexp_of_t_hum = sexp_of_t
      let sexp_of_t t = [%sexp (id t : int)]
    end

    include T

    let next_id = ref (-1)
    let reset_id_cnt () = next_id := -1

    (* [make structure metadata] returns a fresh type w/ structure [structure] and
       metadata [metadata]. *)
    let create structure =
      Union_find.create
        { id =
            (Int.incr next_id;
             !next_id)
        ; structure
        }


    let fold
        (type a)
        type_
        ~(f : t -> a Structure.t -> a)
        ~(var : t -> a)
        ~(mu : t -> a -> a)
        : a
      =
      Log.debug (fun m -> m "Folding over type: %d" (id type_));
      (* Hash table records the variables that are grey ([false])
       or black ([true]). *)
      let table = Hashtbl.create (module T) in
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
          let result = f type_ (structure type_ |> Structure.map ~f:loop) in
          let status = Hashtbl.find_exn table type_ in
          Hashtbl.remove table type_;
          Log.debug (fun m -> m "Loop status %b" status);
          if status
          then mu type_ result
          else (
            Log.debug (fun m -> m "Returning from loop");
            result))
      in
      let result = loop type_ in
      Log.debug (fun m -> m "Finished folding");
      result


    module To_dot = struct
      type 'a state =
        { mutable id : int
        ; buffer : Buffer.t
        }

      let basic_shape ~label () : string =
        let label = String.escaped label in
        [%string {|[style=filled, shape = oval, label = "%{label}"];|}]


      let structure_to_string structure : string =
        Structure.sexp_of_t (fun _ -> Atom "") structure |> Sexp.to_string_hum


      let register state t : string =
        let id = [%string "%{state.id#Int}"] in
        Buffer.add_string state.buffer id;
        Buffer.add_char state.buffer ' ';
        Buffer.add_string
          state.buffer
          (basic_shape ~label:(structure_to_string (structure t)) ());
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
            structure t
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
  let rec unify_exn ~ctx t1 t2 = Union_find.union ~f:(unify_desc ~ctx) t1 t2

  (* [unify_desc desc1 desc2] unifies the descriptors of the graph types
     (of multi-equations). *)
  and unify_desc ~ctx desc1 desc2 =
    { id = desc1.id
    ; structure = unify_structure ~ctx desc1.structure desc2.structure
    }


  (* [unify_structure structure1 structure2] unifies two graph type node
     structures. *)
  and unify_structure ~ctx structure1 structure2 =
    Structure.merge
      ~ctx
      ~create:Type.create
      ~unify:(unify_exn ~ctx)
      structure1
      structure2


  exception Unify of Type.t * Type.t

  let unify ~ctx t1 t2 =
    try unify_exn ~ctx t1 t2 with
    | Structure.Cannot_merge -> raise (Unify (t1, t2))
end
