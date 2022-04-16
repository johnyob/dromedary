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

open Base

(* This module implements an efficient union-find algorithm
   on disjoint sets, based on Tarjan and Huet. See IA notes. *)

(* A disjoint set D is a family of disjoint sets D = {S1, ..., Sn},
  with the following operations:
  - [fresh x] : Creates a new set S containing x in D.
  - [find x] : Returns the (unique) set S_x in D that contains x. 
  - [union x y]: Performs the union of S_x and S_y in D. 
*)

(* A disjoint set D is represeted using a forest, 
   a collection of trees, each node in the tree storing it's value, with 
   pointers to parents. 

   Operations:
   - [find x]: 
      This traverses the element x back to the root of the set. This
      path is known as the find path. We use *path compression*, which simply
      makes each vertex in the find path point directly to the root.

   - [union x y]: 
      We use union by rank. Each set stores the *rank*, the upper bound for the 
      height of the tree. For [union x y], suppose [t_x], [t_y] have ranks 
      [r_x], [r_y]. 
      
      If [r_x < r_y] => [t_x] becomes the child of [t_y]. The resulting rank is 
      given by [if r_x != r_y then max r_x r_y else r_x + 1]. 
*)

(* Our implementation of union-find makes an initial optimization.
   We define a set of nodes, which are partitioned into (disjoint) equivalence 
   classes. Each equivalence class is associated with an abstract value of type 
   ['a], which we call a *descriptor*. 
*)

(* A link [link] is the contents of a node [node]. If [node] is the root of the
   equivalence class, then it contains the rank and descriptor. Otherwise, it 
   contains a pointer to it's parent vertex. 
*)

type 'a link =
  | Root of (* rank *) int * (* descriptor *) 'a
  | Link of 'a t

(* The type ['a t] represents a node in the union-find data structure. *)
and 'a t = 'a link ref [@@deriving sexp_of]

(* [make desc] creates a fresh node. It forms it's own equivalence class, 
   with descriptor [desc] and rank [0]. *)
let make desc = ref (Root (0, desc))

(* [root node] returns the root element of [node]'s equivalence class.
   It is found by traversing pointers. While doing so, we perform 
   path-compression. 
*)
let rec root node =
  match !node with
  | Root _ -> node
  | Link node' ->
    let root' = root node' in
    (* Perform path compression. If [root' = node'], then [node] 
       already points to root. *)
    if not (phys_equal node' root') then node := !node';
    root'


(* [find node] returns the descriptor associated w/ [node]'s 
   equivalence class. 
   
   We could simply have:
   [let find node = 
      match !(root node) with
      | Root (_, desc) -> desc
      | Link _ -> assert false ]
    However, this inefficient for the root, and children of
    the root and requires an [assert false] (which we prefer to avoid).
*)
let rec find node =
  match !node with
  | Root (_, desc) -> desc
  | Link node' ->
    (match !node' with
    | Root (_, desc) -> desc
    | Link _ -> find (root node))


let rec set node desc =
  match !node with
  | Root (rank, _) -> node := Root (rank, desc)
  | Link node' ->
    (match !node' with
    | Root (rank, _) -> node := Root (rank, desc)
    | Link _ -> set (root node) desc)


let link_with ~src ~dst ~f =
  let snapshot = !dst in
  dst := Link src;
  try f () with
  | exn ->
    dst := snapshot;
    raise exn


let link node1 node2 ~f =
  if phys_equal node1 node2
  then ()
  else (
    match !node1, !node2 with
    | Root (rank1, desc1), Root (rank2, desc2) ->
      if rank1 > rank2
      then
        link_with ~src:node1 ~dst:node2 ~f:(fun () ->
            let desc = f desc1 desc2 in
            node1 := Root (rank1, desc))
      else (
        let rank = if rank1 < rank2 then rank1 else rank1 + 1 in
        link_with ~src:node2 ~dst:node1 ~f:(fun () ->
            let desc = f desc1 desc2 in
            node2 := Root (rank, desc)))
    | _ -> assert false)


let union node1 node2 ~f =
  let root1 = root node1
  and root2 = root node2 in
  link root1 root2 ~f


(* [node1 === node2] determines whether [node1] and [node2] are in the same
   equivalence class. *)
let ( === ) node1 node2 =
  phys_equal node1 node2 || phys_equal (root node1) (root node2)

(* 
(* [is_root node] determines whether [node] is a root node. *)
let is_root node =
  match !node with
  | Root _ -> true
  | Link _ -> false


(* [is_child node] determines whether [node] is a child node. *)
let is_child node =
  match !node with
  | Root _ -> false
  | Link _ -> true *)