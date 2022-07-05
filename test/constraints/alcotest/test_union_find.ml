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

let count = 10000

let test_union_nodes_have_equal_descriptors =
  QCheck.Test.make
    ~count
    ~name:"Test union : nodes have equal descriptors"
    QCheck.(pair int int)
    (fun (i, j) ->
      (* Arrange *)
      let node1 = Union_find.create i
      and node2 = Union_find.create j in
      (* Act *)
      Union_find.union node1 node2 ~f:( + );
      (* Assert *)
      Union_find.get node1 = Union_find.get node2)
  |> QCheck_alcotest.to_alcotest


let test_union_descriptor_computation =
  QCheck.Test.make
    ~count
    ~name:"Test union : descriptor computation is correctly parameterized"
    QCheck.(pair int int)
    (fun (i, j) ->
      (* Arrange *)
      let node1 = Union_find.create i
      and node2 = Union_find.create j in
      (* Act *)
      Union_find.union node1 node2 ~f:( - );
      (* Assert *)
      Union_find.get node1 = i - j)
  |> QCheck_alcotest.to_alcotest


let test_union_nodes_are_equiv =
  QCheck.Test.make
    ~count
    ~name:"Test union : nodes belong to same set"
    QCheck.(pair int int)
    (fun (i, j) ->
      (* Arrange *)
      let node1 = Union_find.create i
      and node2 = Union_find.create j in
      (* Act *)
      Union_find.union node1 node2 ~f:( * );
      (* Assert *)
      Union_find.(node1 === node2))
  |> QCheck_alcotest.to_alcotest


let test_find_returns_correct_descriptor =
  QCheck.Test.make
    ~count
    ~name:"Test find : returns correct descriptor"
    QCheck.(int)
    (fun i ->
      (* Arrange *)
      let node = Union_find.create i in
      (* Act *)
      let i' = Union_find.get node in
      (* Assert *)
      i = i')
  |> QCheck_alcotest.to_alcotest


let test_set_sets_descriptor =
  QCheck.Test.make
    ~count
    ~name:"Test set : find (set n x) = x"
    QCheck.(pair int int)
    (fun (i, j) ->
      (* Arrange *)
      let node = Union_find.create i in
      (* Act *)
      Union_find.set node j;
      (* Assert *)
      Union_find.get node = j)
  |> QCheck_alcotest.to_alcotest


let test_equiv_is_reflexive =
  QCheck.Test.make
    ~count
    ~name:"Test === : === is reflexive"
    QCheck.(int)
    (fun i ->
      (* Arrange *)
      let node = Union_find.create i in
      (* Act *)
      (* Assert *)
      Union_find.(node === node))
  |> QCheck_alcotest.to_alcotest

let tests =
  [ ( "Union_find"
    , [ test_union_nodes_have_equal_descriptors
      ; test_union_descriptor_computation
      ; test_union_nodes_are_equiv
      ; test_find_returns_correct_descriptor
      ; test_set_sets_descriptor
      ; test_equiv_is_reflexive
      ] )
  ]
