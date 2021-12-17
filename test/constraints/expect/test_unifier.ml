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

module Type_former = struct
  type 'a t = Constr of 'a list * string [@@deriving sexp_of]

  let map (Constr (ts, constr)) ~f = Constr (List.map ~f ts, constr)
  let iter t ~f = ignore (map t ~f : unit t)
  let fold (Constr (ts, _)) ~f ~init = List.fold_right ~init ~f ts

  exception Iter2

  let iter2_exn t1 t2 ~f =
    match t1, t2 with
    | Constr (ts1, constr1), Constr (ts2, constr2)
      when String.equal constr1 constr2 ->
      (try List.iter2_exn ts1 ts2 ~f with
      | _ -> raise Iter2)
    | _, _ -> raise Iter2
end

module Metadata = struct
  type t = unit [@@deriving sexp_of]

  let merge t1 _ = t1
end

module Unifier = Unifier (Type_former) (Metadata)
module Type = Unifier.Type

let unify = Unifier.unify
let make_var ?(flexibility = Type.Flexible) () = Unifier.make_var flexibility ()
let ( @ ) f ts = Unifier.make_former (Constr (ts, f)) ()

let print_type t =
  let content = Type.to_dot t in
  let out = Stdlib.open_out "/tmp/foo" in
  Stdlib.output_string out content;
  Stdlib.flush out;
  assert (
    Stdlib.Sys.command "graph-easy /tmp/foo --from graphviz --as boxart" = 0)


let%expect_test "Test unify : correctness 1" =
  let t1 = "P" @ [ make_var ~flexibility:Rigid () ]
  and t2 = "P" @ [ make_var () ] in
  unify t1 t2;
  print_type t1;
  [%expect
    {|
    ┌─────────────────┐
    │        !        │
    └─────────────────┘
      │
      │
      ▼
    ┌─────────────────┐
    │ (Constr ("") P) │
    └─────────────────┘ |}]

let%expect_test "Test unify : correctness 2" =
  let t1 = "P" @ [ "f" @ [ make_var ~flexibility:Rigid (); make_var () ] ]
  and t2 =
    let y = make_var () in
    "P" @ [ "f" @ [ y; "g" @ [ y ] ] ]
  in
  unify t1 t2;
  print_type t1;
  [%expect
    {|
    ┌────────────────────┐
    │         !          │ ─┐
    └────────────────────┘  │
      │                     │
      │                     │
      ▼                     │
    ┌────────────────────┐  │
    │  (Constr ("") g)   │  │
    └────────────────────┘  │
      │                     │
      │                     │
      ▼                     │
    ┌────────────────────┐  │
    │ (Constr ("" "") f) │ ◀┘
    └────────────────────┘
      │
      │
      ▼
    ┌────────────────────┐
    │  (Constr ("") P)   │
    └────────────────────┘ |}]

let%expect_test "Test unify : correctness 3" =
  let t1 =
    let y = make_var () in
    "P" @ [ y; "f" @ [ y ] ]
  and t2 =
    let x = make_var () in
    "P" @ [ x; x ]
  in
  unify t1 t2;
  print_type t1;
  [%expect
    {|
       ┌────────────────────┐
    ┌▶ │ (Constr ("" "") P) │
    │  └────────────────────┘
    │    ▲
    │    │
    │    │
    │  ┌────────────────────┐
    │  │                    │ ───┐
    │  │  (Constr ("") f)   │    │
    └─ │                    │ ◀──┘
       └────────────────────┘ |}]

