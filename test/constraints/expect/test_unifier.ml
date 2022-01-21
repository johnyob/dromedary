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
  module T = struct
    type 'a t = Constr of 'a list * string [@@deriving sexp_of]

    let id (Constr (_, constr)) = String.hash constr

    module Traverse (F : Applicative.S) = struct
      open F

      let traverse (Constr (ts, constr)) ~f =
        all (List.map ~f ts) >>| fun ts -> Constr (ts, constr)


      let traverse2 (Constr (ts1, constr1)) (Constr (ts2, constr2)) ~f =
        let open List.Or_unequal_lengths in
        if String.(constr1 = constr2)
        then (
          match List.map2 ts1 ts2 ~f with
          | Ok ts -> `Ok (all ts >>| fun ts -> Constr (ts, constr1))
          | Unequal_lengths -> `Unequal_structure)
        else `Unequal_structure
    end
  end

  include T
  include Type_former.Make (T)
end

module Metadata = struct
  type t = unit [@@deriving sexp_of]

  let merge t1 _ = t1
end

module Unifier =
  Unifier (Structure.First_order (Structure.Of_former (Type_former)))

module Type = Unifier.Type

let unify = Unifier.unify ~expansive:() ~ctx:()
let make_flexible_var () = Unifier.Type.make Var

let make_rigid_var =
  let next_rigid = ref (-1) in
  fun () -> Unifier.Type.make
    (Structure
       (Constr
          ( []
          , "rigid"
            ^
            (Int.incr next_rigid;
             Int.to_string !next_rigid) )))


let ( @ ) f ts = Unifier.Type.make (Structure (Constr (ts, f)))

let print_type t =
  let content = Type.to_dot t in
  let out = Stdlib.open_out "/tmp/foo" in
  Stdlib.output_string out content;
  Stdlib.flush out;
  assert (
    Stdlib.Sys.command "graph-easy /tmp/foo --from graphviz --as boxart" = 0)


let%expect_test "Test unify : correctness 1" =
  let t1 = "P" @ [ make_rigid_var () ]
  and t2 = "P" @ [ make_flexible_var () ] in
  unify t1 t2;
  print_type t1;
  [%expect
    {|
      ┌────────────────────────────────┐
      │ (Structure (Constr () rigid0)) │
      └────────────────────────────────┘
        │
        │
        ▼
      ┌────────────────────────────────┐
      │  (Structure (Constr ("") P))   │
      └────────────────────────────────┘ |}]

let%expect_test "Test unify : correctness 2" =
  let t1 = "P" @ [ "f" @ [ make_rigid_var (); make_flexible_var () ] ]
  and t2 =
    let y = make_flexible_var () in
    "P" @ [ "f" @ [ y; "g" @ [ y ] ] ]
  in
  unify t1 t2;
  print_type t1;
  [%expect
    {|
      ┌────────────────────────────────┐
      │ (Structure (Constr () rigid1)) │ ─┐
      └────────────────────────────────┘  │
        │                                 │
        │                                 │
        ▼                                 │
      ┌────────────────────────────────┐  │
      │  (Structure (Constr ("") g))   │  │
      └────────────────────────────────┘  │
        │                                 │
        │                                 │
        ▼                                 │
      ┌────────────────────────────────┐  │
      │ (Structure (Constr ("" "") f)) │ ◀┘
      └────────────────────────────────┘
        │
        │
        ▼
      ┌────────────────────────────────┐
      │  (Structure (Constr ("") P))   │
      └────────────────────────────────┘ |}]

let%expect_test "Test unify : correctness 3" =
  let t1 =
    let y = make_flexible_var () in
    "P" @ [ y; "f" @ [ y ] ]
  and t2 =
    let x = make_flexible_var () in
    "P" @ [ x; x ]
  in
  unify t1 t2;
  print_type t1;
  [%expect
    {|
         ┌────────────────────────────────┐
      ┌▶ │ (Structure (Constr ("" "") P)) │
      │  └────────────────────────────────┘
      │    ▲
      │    │
      │    │
      │  ┌────────────────────────────────┐
      │  │                                │ ───┐
      │  │  (Structure (Constr ("") f))   │    │
      └─ │                                │ ◀──┘
         └────────────────────────────────┘ |}]
