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
      { hash : int
      ; type_ : Type.t list * Type.t Former.t
      ; productivity : productivity
      ; decomposable_positions : int list
      ; rank : int
      }

    and productivity =
      | Non_productive of int
      | Productive of Type.t Former.t

    let make ~former ~rank ~decomposable_positions ~productivity ~type_ =
      { hash = Former.hash former
      ; rank
      ; productivity
      ; decomposable_positions
      ; type_
      }


    let hash t = t.hash
    let type_ t = t.type_
    let productivity t = t.productivity
    let decomposable_positions t = t.decomposable_positions
    let rank t = t.rank
  end

  module Ctx = struct
    type t =
      { abbreviations : (int, Abbreviation.t, Int.comparator_witness) Map.t }

    let empty = { abbreviations = Map.empty (module Int) }

    let add t ~abbrev =
      { abbreviations =
          Map.set t.abbreviations ~key:(Abbreviation.hash abbrev) ~data:abbrev
      }


    let has_abbrev t former = Map.mem t.abbreviations (Former.hash former)

    exception Not_found

    let find_abbrev t former =
      match Map.find t.abbreviations (Former.hash former) with
      | Some abbrev -> abbrev
      | None -> raise Not_found


    type productivity =
      | Non_productive of int
      | Productive

    let get_productivity t former =
      let abbrev = find_abbrev t former in
      match Abbreviation.productivity abbrev with
      | Abbreviation.Non_productive i -> Non_productive i
      | Abbreviation.Productive _ -> Productive


    let get_expansion t former = find_abbrev t former |> Abbreviation.type_

    let get_decomposable_positions t former =
      match Map.find t.abbreviations (Former.hash former) with
      | Some abbrev -> Abbreviation.decomposable_positions abbrev
      | None ->
        List.range ~start:`inclusive ~stop:`exclusive 0 (Former.length former)


    let get_rank t former =
      match Map.find t.abbreviations (Former.hash former) with
      | Some abbrev -> Abbreviation.rank abbrev
      | None -> 0


    let clash t former1 former2 =
      let open Abbreviation in
      let former former =
        let abbrev = Map.find t.abbreviations (Former.hash former) in
        match abbrev with
        | Some abbrev ->
          (match productivity abbrev with
          | Productive former -> Former.hash former
          | _ -> assert false)
        | None -> Former.hash former
      in
      let former1 = former former1
      and former2 = former former2 in
      former1 <> former2
  end
end