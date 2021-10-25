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
  (* TODO: Investigate usage of variable_kind at the type level *)

  (* Unification involves [variable]s, using the union-find data structure. *)

  (* A variable is either flexible or rigid.
     A flexible variable may be unified with other types / variables.
     Whereas a rigid variable cannot, it acts as a "skolem constant". *)

  type variable_kind =
    | Flexible
    | Rigid
  [@@deriving sexp_of, eq]

  type variable = variable_desc Union_find.t [@@deriving sexp_of]

  (* Unification descriptors contain information related to the variable.
   
     Variables may be viewed as pointers into "multi-equitions", since
     [Union_find.node] denotes a node in an equivalence class, with 
     descriptors describing the equivalence class. 

    Every multi-equation is assigned a global identifier [id].
    On [fresh], an identifier is allocated. On [union], an arbitrary
    identifier is used from the 2 arguments.
    
    Every multi-equation contains a set of variables of a given 
    [kind]. See {!variable_kind}.

    Every multi-equation is either standard, or non-standard. 
    In a non-standard multi-equation, there is no terminal,
    hence the field [terminal] is [None]. In a standard multi-equvation
    [terminal] is [Some t], where [t] is the non-variable member of the 
    equation. 
    
    Note that we use "shallow-types" (namely type formers whose arguments
    are variables), this is an optimization. *)
  and variable_desc =
    { id : int
    ; kind : variable_kind
    ; mutable terminal : variable Former.t option
    ; mutable metadata : Metadata.t
    }

  (* ------------------------------------------------------------------------- *)

  (* Setters and Getters *)

  let id var = (Union_find.find var).id
  let kind var = (Union_find.find var).kind
  let get_terminal var = (Union_find.find var).terminal
  let set_terminal var terminal = (Union_find.find var).terminal <- terminal
  let get_metadata var = (Union_find.find var).metadata
  let set_metadata var metadata = (Union_find.find var).metadata <- metadata

  (* ------------------------------------------------------------------------- *)

  (* [is_rigid var] returns true if [var] is a rigid variable. *)
  let is_rigid var =
    match kind var with
    | Rigid -> true
    | Flexible -> false


  (* [is_flexible] returns true if [var] is a flexible variable. *)
  let is_flexible var =
    match kind var with
    | Flexible -> true
    | Rigid -> false


  (* [is_unifiable_desc desc1 desc2] determines whether 2
     multi-equations w/ descriptors [desc1] [desc2] can be unified.  *)
  let is_unifiable_desc desc1 desc2 =
    (* There are 2 cases where rigid variables may be unified:
        - a : Rigid, a : Rigid 
        - a : Rigid, 'a : Flexible and 'a is belongs to a 
          non-standard multi-equation. 
          
       The first case is handled by {union_find.ml}. *)
    not
      ((equal_variable_kind desc1.kind Rigid && Option.is_some desc2.terminal)
      || (equal_variable_kind desc2.kind Rigid && Option.is_some desc1.terminal)
      )


  (* [merge_kind_desc desc1 desc2] computes the resultant kind
     of the multi-equation after unification. *)
  let merge_kind_desc desc1 desc2 =
    match desc1.kind, desc2.kind with
    | Rigid, _ | _, Rigid -> Rigid
    | _ -> Flexible


  (* ------------------------------------------------------------------------- *)

  (* See: https://github.com/janestreet/base/issues/121 *)
  let post_incr r =
    let result = !r in
    Int.incr r;
    result


  (* [fresh kind ?terminal ~metadata ()] creates a fresh variable. *)
  let fresh =
    let id = ref 0 in
    fun kind ?terminal ~metadata () ->
      Union_find.fresh { id = post_incr id; kind; terminal; metadata }


  (* TODO: fresh_list *)

  (* ------------------------------------------------------------------------- *)

  exception Unify_desc
  exception Unify of variable * variable

  let rec unify_ = Union_find.union ~f:unify_desc

  and unify_desc desc1 desc2 =
    if is_unifiable_desc desc1 desc2
    then
      { id = desc1.id
      ; kind = merge_kind_desc desc1 desc2
      ; terminal = unify_terminal desc1.terminal desc2.terminal
      ; metadata = Metadata.merge desc1.metadata desc2.metadata
      }
    else raise Unify_desc


  and unify_terminal terminal1 terminal2 =
    Option.merge
      ~f:(fun typ1 typ2 ->
        Former.iter2 ~f:unify_ typ1 typ2;
        typ1)
      terminal1
      terminal2


  let unify var1 var2 =
    try unify_ var1 var2 with
    | _ -> raise (Unify (var1, var2))


  (* ------------------------------------------------------------------------- *)

  (* [compare_variable var1 var2] computes the ordering of [var1, var2],
     based on their unique identifiers. *)

  let compare_variable var1 var2 = Int.compare (id var1) (id var2)

  (* [hash var] computes the hash of the variable [var]. 
     Based on it's integer field: id. *)

  let hash var = Hashtbl.hash (id var)

  (* [Variable_hash_key] is a module implementation for [Hashtbl.Key.S]
     for variables. 
     
     We extensively make use of efficient (imperivative) datastructures
     such as [Hashtbl] or [Hash_set]. *)

  module Variable_hash_key : Hashtbl.Key.S with type t = variable = struct
    type t = variable

    let compare = compare_variable
    let hash = hash
    let sexp_of_t = sexp_of_variable
  end

  (* ------------------------------------------------------------------------- *)

  exception Cycle of variable

  (* [occurs_check var] detects whether there is 
     a cycle in the multi-equation associated with [var]. 
      
     If a cycle is detected, [Cycle var] is raised.
     
     It is named [occurs_check] for historical reasons. *)

  let occurs_check =
    (* Hash table records the variables that are grey ([false])
       or black ([true]). *)
    let table = Hashtbl.create (module Variable_hash_key) in
    (* Recursive loop that traverses the graph, checking 
       for cycles. *)
    let rec loop var =
      try
        (* We raise an exception [Not_found_s] instead of using
           an option, since it is more efficient.
           
           No heap allocation. *)
        let visited = Hashtbl.find_exn table var in
        (* A cycle has occurred is the variable is grey. *)
        if not visited then raise (Cycle var)
      with
      | Not_found_s _ ->
        (* Mark this variable as grey. *)
        Hashtbl.set table ~key:var ~data:false;
        (* Visit children *)
        Option.iter ~f:(Former.iter ~f:loop) (get_terminal var);
        (* Mark this variable as black. *)
        Hashtbl.set table ~key:var ~data:true
    in
    loop


  (* ------------------------------------------------------------------------- *)

  (* [fold var ~leaf ~node ~init] will perform a bottom-up fold
     over the (assumed) acyclic graph defined by the variable [var]. 
     
     [leaf] is performed when we reach a variable with no terminal (a leaf).
     [node] is performed when we reach a variable with a terminal (a node).
     [init] is the initial accumulator value. *)

  let fold
      (type a)
      var
      ~(leaf : variable -> a)
      ~(node : a Former.t -> a)
      : a
    =
    (* Hash table records whether variable has been visited, and 
       it's computed value. *)
    let visited : (variable, a) Hashtbl.t =
      Hashtbl.create (module Variable_hash_key)
    in
    (* Recursive loop, folding over the graph, with accumulator
       [acc]. *)
    let rec loop var =
      try Hashtbl.find_exn visited var with
      | Not_found_s _ ->
        let result =
          match get_terminal var with
          | None -> leaf var
          | Some t -> node (Former.map ~f:loop t)
        in
        (* We assume we can set [var] in [visited] *after* traversing
           it's children, since the graph is acyclic. *)
        Hashtbl.set visited ~key:var ~data:result;
        result
    in
    loop var
end
