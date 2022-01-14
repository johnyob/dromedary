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

open Core

module Elt = struct
  type 'a t =
    { mutable value : 'a
    ; mutable next : 'a t option
    ; mutable prev : 'a t option
    }
  [@@deriving sexp_of]

  let unlink t =
    t.next <- None;
    t.prev <- None


  let make value = { value; next = None; prev = None }
  let get_value t = t.value
  let set_value t value = t.value <- value
end

type 'a t =
  { mutable first : 'a Elt.t option
  ; mutable last : 'a Elt.t option
  }
[@@deriving sexp_of]

let empty () = { first = None; last = None }
let first t = t.first

let remove t elt =
  let Elt.{ prev; next; _ } = elt in
  (match prev with
  | Some prev -> prev.next <- next
  | None -> t.first <- next);
  (match next with
  | Some next -> next.prev <- prev
  | None -> t.last <- prev);
  Elt.unlink elt


let remove_first t =
  let first = first t in
  match first with
  | None -> None
  | Some first ->
    remove t first;
    Some (Elt.get_value first)


let insert_first t elt =
  Elt.(elt.next <- t.first);
  (match t.first with
  | Some first -> first.prev <- Some elt
  | None -> ());
  t.first <- Some elt


let insert_first_elt t x =
  let elt = Elt.make x in
  insert_first t elt;
  elt


let merge t1 t2 ~compare =
  let rec loop t1 t2 =
    match t1.first, t2.first with
    | None, _ -> t2
    | _, None -> t1
    | Some first1, Some first2 ->
      if compare (Elt.get_value first1) (Elt.get_value first2) < 0
      then (
        ignore (remove_first t1 : _ option);
        let result = loop t1 t2 in
        insert_first result first1;
        result)
      else (
        ignore (remove_first t2 : _ option);
        let result = loop t1 t2 in
        insert_first result first2;
        result)
  in
  loop t1 t2
