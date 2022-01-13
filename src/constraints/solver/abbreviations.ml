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
include Abbreviations_intf

module Make (Former : Type_former.S) = struct
  module Type = struct
    type t = desc ref [@@deriving sexp_of]

    and desc =
      { id : int
      ; structure : structure
      }

    and structure =
      | Var
      | Former of t Former.t

    let id t = !t.id
    let get_structure t = !t.structure
    let compare t1 t2 = Int.compare (id t1) (id t2)
    let hash = id

    let post_incr r =
      let result = !r in
      Int.incr r;
      result


    let make =
      let id = ref 0 in
      fun structure -> ref { id = post_incr id; structure }


    let make_var () = make Var
    let make_former former = make (Former former)
  end

  module Abbreviation = struct
    type t =
      { type_ : Type.t list * Type.t Former.t
      ; productivity : productivity
      ; decomposable_positions : int list
      ; rank : int
      }

    (** surpress unused warning. *)
    and productivity =
      | Non_productive of int
      | Productive of Type.t Former.t
    [@@warning "-37"]
  end

  type t =
    { abbreviations : (int, Abbreviation.t, Int.comparator_witness) Map.t }

  let empty = { abbreviations = Map.empty (module Int) }

  type productivity =
    | Non_productive of int
    | Productive
    | Primitive

  let get_productivity t former =
    match Map.find t.abbreviations (Former.hash former) with
    | Some abbrev ->
      (match Abbreviation.(abbrev.productivity) with
      | Abbreviation.Non_productive i -> Non_productive i
      | Abbreviation.Productive _ -> Productive)
    | None -> Primitive


  let get_expansion t former =
    let open Option in
    Map.find t.abbreviations (Former.hash former)
    >>| fun abbrev -> Abbreviation.(abbrev.type_)


  let clash t former1 former2 =
    let abbrev1 = Map.find_exn t.abbreviations (Former.hash former1)
    and abbrev2 = Map.find_exn t.abbreviations (Former.hash former2) in
    Abbreviation.(
      match abbrev1.productivity, abbrev2.productivity with
      | Productive former1', Productive former2' ->
        Former.hash former1' <> Former.hash former2'
      | _ -> assert false)


  let get_decomposable_positions t former =
    let open Option in
    Map.find t.abbreviations (Former.hash former)
    >>| fun abbrev -> Abbreviation.(abbrev.decomposable_positions)


  let get_rank t former =
    let open Option in
    Map.find t.abbreviations (Former.hash former)
    >>| (fun abbrev -> Abbreviation.(abbrev.rank))
    |> value ~default:0
end