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

(* Unification consists of solving equations between types. 
   For generalization and efficiency, we use "multi-equations":
    e ::= [] | t = e
   
   A multi-equation is standard iff it contains 1 non-variable member,
   known as the [terminal]. *)

open Base
open Intf

(* ------------------------------------------------------------------------- *)

(* Include module types and type definitions from the [_intf] file. *)

include Unifier_intf

(* ------------------------------------------------------------------------- *)

module Make (Former : Type_former) (Metadata : Metadata) :
  S with type 'a former := 'a Former.t and type metadata := Metadata.t = struct
  (* Unification involves unification types, using the union-find 
     data structure. 
     
     These are referred to as "graph types" in the dissertation. 
     While are formalization doesn't exactly match our implementation, 
     the notion provides useful insight. *)

  module Type = struct
    (* A variable is either flexible or rigid.

       A flexible variable may be unified with other types / variables.
       Whereas a rigid variable cannot, it acts as a "skolem constant". *)

    type flexibility =
      | Flexible
      | Rigid
    [@@deriving sexp_of, eq]

    (* A graph type consists of a [Union_find] node,
       allowing reasoning w/ multi-equations of nodes. *)

    type t = desc Union_find.t [@@deriving sexp_of]

    (* Graph type node descriptors contain information related to the 
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
       are implemented here. *)
    and desc =
      { id : int
      ; mutable structure : structure
      ; mutable metadata : Metadata.t
      }

    (* Graph type node structures are either variables or type
       formers. 
       
       A variable denotes it's flexibility, using {!flexibility}.
       This is required for unification under a mixed prefix. *)
    and structure =
      | Var of { mutable flexibility : flexibility }
      | Form of t Former.t

    (* --------------------------------------------------------------------- *)

    (* Setters and Getters *)

    let id t = (Union_find.find t).id
    let get_structure t = (Union_find.find t).structure
    let set_structure t structure = (Union_find.find t).structure <- structure
    let get_metadata t = (Union_find.find t).metadata
    let set_metadata t metadata = (Union_find.find t).metadata <- metadata

    (* --------------------------------------------------------------------- *)

    (* [compare t1 t2] computes the ordering of [t1, t2],
      based on their unique identifiers. *)

    let compare t1 t2 = Int.compare (id t1) (id t2)

    (* [hash t] computes the hash of the graph type [t]. 
       Based on it's integer field: id. *)

    let hash t = Hashtbl.hash (id t)
  end

  open Type

  (* ----------------------------------------------------------------------- *)

  (* See: https://github.com/janestreet/base/issues/121 *)
  let post_incr r =
    let result = !r in
    Int.incr r;
    result


  (* [fresh structure metadata] creates a fresh node. *)
  let fresh =
    let id = ref 0 in
    fun structure metadata ->
      Union_find.fresh { id = post_incr id; structure; metadata }


  (* TODO: fresh_list *)

  (* [fresh_var flexibility metadata] creates a fresh variable node. *)
  let fresh_var flexibility metadata = fresh (Var { flexibility }) metadata

  (* [fresh_form form metadata] creates a fresh type former node. *)
  let fresh_form form metadata = fresh (Form form) metadata

  (* ----------------------------------------------------------------------- *)

  exception Unify_rigid

  (* [unify_exn] unifies two graph types. No exception handling is 
     performed here. This is an internal function.
     
     Possible exceptions include:
     - [Former.Iter2], raised when executing Former.iter2 in {unify_form}.
     - [Unify_rigid], raised when incorrectly unifying a rigid variable.

     See {!unify}. *)

  let rec unify_exn = Union_find.union ~f:unify_desc

  (* ----------------------------------------------------------------------- *)

  (* [unify_desc desc1 desc2] unifies the descriptors of the graph types
     (of multi-equations). *)

  and unify_desc desc1 desc2 =
    { id = desc1.id
    ; structure = unify_structure desc1.structure desc2.structure
    ; metadata = Metadata.merge desc1.metadata desc2.metadata
    }

  (* ----------------------------------------------------------------------- *)

  (* [unify_structure structure1 structure2] unifies two graph type node
     structures. We handle rigid variables here. *)

  and unify_structure structure1 structure2 =
    match structure1, structure2 with
    (* Unification of variables. *)

    (* Unification is permitted between distinct variables only if 
       both variables are *not* rigid.
  
       In the case of 2 rigid variable, we raise [Unify_rigid].

       We may unify a rigid variable with itself. However, this case does 
       not arise here since [Union_find.union] checks physical equality 
       before before [unify_structure] is executed. *)

    | Var { flexibility = Rigid }, Var { flexibility = Rigid } ->
      raise Unify_rigid
    
    | Var { flexibility = Rigid }, Var { flexibility = Flexible }
    | Var { flexibility = Flexible }, Var { flexibility = Rigid } ->
      Var { flexibility = Rigid }
    
    | Var { flexibility = Flexible }, Var { flexibility = Flexible } ->
      Var { flexibility = Flexible }

    (* Unification of variables (leaves) and type formers (internal nodes). *)

    (* We may unify a flexible variable with a type former, yielding
       the same type former. 

       Note that no propagation of metadata is performed. This is required
       by external modules. See {!generalization.ml}. *)
    | Var { flexibility = Flexible }, Form form
    
    (* Unification between a rigid variable and a type former is not 
       permitted. We raise [Unify_rigid]. *)
    
    | Form form, Var { flexibility = Flexible } -> Form form
    | Var { flexibility = Rigid }, Form _ | Form _, Var { flexibility = Rigid }
      -> raise Unify_rigid 
    
    (* Unification between type formers. *)
    
    (* We may unify type formers recursively. See {!unify_form}. *)
    | Form form1, Form form2 -> Form (unify_form form1 form2)


  (* ----------------------------------------------------------------------- *)

  (* [unify_form form1 form2] recursively unifies 2 type formers.

     Here we use our internal unification function [unify_exn],
     to allow exception propagation to the top-level call. *)

  and unify_form form1 form2 =
    Former.iter2 ~f:unify_exn form1 form2;
    form1


  (* ----------------------------------------------------------------------- *)

  exception Unify of Type.t * Type.t

  let unify t1 t2 =
    try unify_exn t1 t2 with
    | Former.Iter2 | Unify_rigid -> raise (Unify (t1, t2))


  (* ----------------------------------------------------------------------- *)

  exception Cycle of Type.t

  (* [occurs_check t] detects whether there is 
     a cycle in the graph type [t]. 
      
     If a cycle is detected, [Cycle t] is raised.
     
     It is named [occurs_check] for historical reasons. *)

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
           
           No heap allocation. *)
        let visited = Hashtbl.find_exn table t in
        (* A cycle has occurred is the variable is grey. *)
        if not visited then raise (Cycle t)
      with
      | Not_found_s _ ->
        (match get_structure t with
        | Var _ ->
          (* A variable is a leaf. Hence no traversal is
             required, so simply mark as visited. *)
          Hashtbl.set table ~key:t ~data:true
        | Form form ->
          (* Mark this node as grey. *)
          Hashtbl.set table ~key:t ~data:false;
          (* Visit children *)
          Former.iter ~f:loop form;
          (* Mark this variable as black. *)
          Hashtbl.set table ~key:t ~data:true)
    in
    loop
end
