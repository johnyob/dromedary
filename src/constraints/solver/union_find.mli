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

open! Import

(** This module implements an efficient union-find algorithm
    on disjoint sets, based on Tarjan and Huet. See IA Algorithms notes. *)

(** The type ['a t] denotes a node within a given disjoint set. 
    ['a] is the type of the value (descriptor) of the node. *)

type 'a t [@@deriving sexp_of]

(** [make desc] creates a make node. It forms it's disjoint set, with 
    descriptor [desc]. *)
val make : 'a -> 'a t

(** [find node] returns the descriptor associated w/ [node]'s set. *)
val find : 'a t -> 'a

(** [set node desc] updates the descriptor of [node] to [desc]. *)
val set : 'a t -> 'a -> unit

(** [union node1 node2 ~f] merges the disjoint sets associated with [node1]
    and [node2]. The descriptors are merged using the function [~f]. *)
val union : 'a t -> 'a t -> f:('a -> 'a -> 'a) -> unit

(** [node1 === node2] returns true if [node1] and [node2] belong to the same
    disjoint set. *)
val ( === ) : 'a t -> 'a t -> bool

val is_child : 'a t -> bool

val is_root : 'a t -> bool

