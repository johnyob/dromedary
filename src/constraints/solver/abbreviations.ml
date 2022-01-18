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

module Make (Former : Type_former.S) (Metadata : Unifier.Metadata.S) = struct
  module Abbrev_type = struct
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
      { id : int
      ; type_ : Abbrev_type.t list * Abbrev_type.t Former.t
      ; productivity : productivity
      ; decomposable_positions : int Hash_set.t
      ; rank : int
      }

    and productivity =
      | Non_productive of int
      | Productive of int

    let make ~former ~rank ~decomposable_positions ~productivity ~type_ =
      { id = Former.id former
      ; rank
      ; productivity =
          (match productivity with
          | `Non_productive i -> Non_productive i
          | `Productive former -> Productive (Former.id former))
      ; decomposable_positions =
          Hash_set.of_list (module Int) decomposable_positions
      ; type_
      }


    let id t = t.id
    let type_ t = t.type_
    let productivity t = t.productivity
    let decomposable_positions t = t.decomposable_positions
    let rank t = t.rank
  end

  module Non_productive_view = struct
    type 'a t = 'a Former.t Hash_set.t [@@deriving sexp_of]

    let repr t = Hash_set.find t ~f:(fun _ -> true)
    let iter t ~f = Hash_set.iter t ~f:(Former.iter ~f)

    let fold t ~f ~init =
      Hash_set.fold t ~init ~f:(fun acc former ->
          Former.fold former ~init:acc ~f)


    let merge t1 t2 = Hash_set.union t1 t2
    let add t former = Hash_set.add t former
  end

  module Productive_view = struct
    module Elt = struct
      type 'a t =
        { former : 'a Former.t
        ; rank : int
        }
      [@@deriving sexp_of]

      let get_former t = t.former
      let get_rank t = t.rank
      let map t ~f = { t with former = Former.map t.former ~f }
      let set_former t former = { t with former }
    end

    module Ctx = struct
      type 'a t =
        { abbreviations : (Int.t, Abbreviation.t, Int.comparator_witness) Map.t
        ; productive_convert : Abbreviation.t -> 'a Array.t * 'a Former.t
        }

      let sexp_of_t _ _ = Sexp.Atom "Abbreviation Ctx"
      let has_abbrev t former_id = Map.mem t.abbreviations former_id

      exception Not_found

      let find_abbrev t former_id =
        match Map.find t.abbreviations former_id with
        | Some abbrev -> abbrev
        | None -> raise Not_found


      let get_expansion t former_id =
        find_abbrev t former_id |> t.productive_convert


      let get_decomposable_positions t former_id =
        find_abbrev t former_id |> Abbreviation.decomposable_positions


      (* let get_productivity t former_id =
        find_abbrev t former_id |> Abbreviation.productivity *)

      let get_rank t former_id =
        match Map.find t.abbreviations former_id with
        | Some abbrev -> Abbreviation.rank abbrev
        | None -> 0


      let clash t former_id1 former_id2 =
        let open Abbreviation in
        let former former_id =
          let abbrev = Map.find t.abbreviations former_id in
          match abbrev with
          | Some abbrev ->
            (match productivity abbrev with
            | Productive former_id -> former_id
            | _ -> assert false)
          | None -> former_id
        in
        let former1 = former former_id1
        and former2 = former former_id2 in
        former1 <> former2
    end

    type 'a t =
      { mutable repr : 'a desc
      ; mutable expansive : 'a Elt.t Doubly_linked.t
      ; mutable elts : (int, 'a desc) Hashtbl.t
      }
    [@@deriving sexp_of]

    and 'a desc =
      | Non_expansive of 'a Elt.t
      | Expansive of 'a Elt.t Doubly_linked.Elt.t

    let elt_of_desc desc =
      match desc with
      | Non_expansive elt -> elt
      | Expansive dl_elt -> Doubly_linked.Elt.get_value dl_elt


    let singleton ~kind elt =
      let expansive = Doubly_linked.empty () in
      let desc =
        match kind with
        | `Non_expansive -> Non_expansive elt
        | `Expansive -> Expansive (Doubly_linked.insert_first_elt expansive elt)
      in
      let elts = Hashtbl.create (module Int) in
      Hashtbl.set elts ~key:(Former.id (Elt.get_former elt)) ~data:desc;
      { repr = desc; expansive; elts }


    let rank_of_desc desc = elt_of_desc desc |> Elt.get_rank
    let repr t = t.repr |> elt_of_desc |> Elt.get_former

    let iter t ~f =
      let f elt = Former.iter ~f (Elt.get_former elt) in
      Doubly_linked.iter t.expansive ~f;
      Hashtbl.iter t.elts ~f:(function
          | Expansive _ -> ()
          | Non_expansive elt -> f elt)


    let fold t ~f ~init =
      let f elt init = Elt.get_former elt |> Former.fold ~f ~init in
      let init = Doubly_linked.fold t.expansive ~init ~f in
      Hashtbl.fold t.elts ~init ~f:(fun ~key:_ ~data acc ->
          match data with
          | Expansive _ -> acc
          | Non_expansive elt -> f elt acc)


    let map t ~f =
      let f = Elt.map ~f in
      (* Map over [expansive]. *)
      let expansive = Doubly_linked.map t.expansive ~f in
      (* Create a new [elts] table. *)
      let elts = Hashtbl.create (module Int) in
      (* Add the elements of [expansive] to [elts]. *)
      Doubly_linked.unsafe_iter expansive ~f:(fun dl_elt ->
          let former_id =
            Doubly_linked.Elt.get_value dl_elt |> Elt.get_former |> Former.id
          in
          Hashtbl.set elts ~key:former_id ~data:(Expansive dl_elt));
      (* Add the non-expansive elements to [elts]. *)
      Hashtbl.iter t.elts ~f:(function
          | Non_expansive elt ->
            let former_id = Elt.get_former elt |> Former.id in
            Hashtbl.set elts ~key:former_id ~data:(Non_expansive (f elt))
          | Expansive _ -> ());
      (* Find the new reprensative *)
      let former_id = elt_of_desc t.repr |> Elt.get_former |> Former.id in
      let repr = Hashtbl.find_exn elts former_id in
      (* Return the new view. *)
      { repr; expansive; elts }


    let find_former t id =
      Hashtbl.find_exn t.elts id |> elt_of_desc |> Elt.get_former


    exception Iter2

    let merge_former ~ctx t1 t2 former_id ~f =
      (* Compute the merged former descriptor *)
      let former : _ Former.t =
        let former1 = find_former t1 former_id
        and former2 = find_former t2 former_id in
        if Ctx.has_abbrev ctx former_id
        then (
          let decomposable_positions : int Hash_set.t =
            Ctx.get_decomposable_positions ctx former_id
          in
          (* Iterate over decomposable positions *)
          let i = ref 0 in
          Former.iter2_exn former1 former2 ~f:(fun t1 t2 ->
              if Hash_set.mem decomposable_positions !i then f t1 t2;
              i := !i + 1))
        else Former.iter2_exn former1 former2 ~f;
        former1
      in
      (* We now determine the structure of the former descriptor *)
      let desc =
        match Hashtbl.find_exn t1.elts former_id with
        | Non_expansive elt -> Non_expansive (Elt.set_former elt former)
        | Expansive dl_elt ->
          let elt = Doubly_linked.Elt.get_value dl_elt in
          Doubly_linked.Elt.set_value dl_elt (Elt.set_former elt former);
          Expansive dl_elt
      in
      desc


    let merge_elts t1 t2 =
      let expansive =
        Doubly_linked.merge
          t1.expansive
          t2.expansive
          ~compare:(fun desc1 desc2 -> Int.compare desc1.rank desc2.rank)
      in
      let elts =
        Hashtbl.merge t1.elts t2.elts ~f:(fun ~key:_ data ->
            match data with
            | `Left desc | `Right desc -> Some desc
            | `Both (desc1, desc2) ->
              (* In the case of a expansive descriptor, we must
                 remove it from the sorted expansive list. *)
              (match desc2 with
              | Non_expansive _ -> ()
              | Expansive dl_elt -> Doubly_linked.remove expansive dl_elt);
              Some desc1)
      in
      expansive, elts


    exception Cannot_merge

    (* [merge ~ctx t1 t2 ~f] attempts to merge [t1] and [t2], executing
       [f] on the decomposable parameters of the common former. *)
    let merge ~ctx t1 t2 ~f =
      (* Determine whether there is a common former w/ id [former_id]
         in [t1] and [t2]. *)
      let former_id =
        (* Determines whether there is common former by computing intersection
           of [elts] keys.
           
           Hack: [fun _ -> true] used to select and arbitrary former. *)
        Hash_set.inter
          (Hash_set.of_hashtbl_keys t1.elts)
          (Hash_set.of_hashtbl_keys t2.elts)
        |> Hash_set.find ~f:(fun _ -> true)
      in
      match former_id with
      | None -> raise Cannot_merge
      | Some former_id ->
        (* Merge the former *)
        let desc = merge_former ~ctx t1 t2 former_id ~f in
        Hashtbl.set t1.elts ~key:former_id ~data:desc;
        (* Merge the elements *)
        let expansive, elts = merge_elts t1 t2 in
        (* Merge the representative *)
        let repr =
          if rank_of_desc t1.repr <= rank_of_desc t2.repr
          then t1.repr
          else t2.repr
        in
        (* Update references (is this necessary?) *)
        t1.repr <- repr;
        t2.repr <- repr;
        t1.expansive <- expansive;
        t2.expansive <- expansive;
        t1.elts <- elts;
        t2.elts <- elts


    let clash ~ctx t1 t2 =
      let formers1 = Hashtbl.keys t1.elts in
      let formers2 = Hashtbl.keys t2.elts in
      List.cartesian_product formers1 formers2
      |> List.exists ~f:(fun (former1, former2) ->
             Ctx.clash ctx former1 former2)


    exception Cannot_expand

    let get_expansive_view t1 t2 =
      match
        Doubly_linked.first t1.expansive, Doubly_linked.first t2.expansive
      with
      | None, None ->
        (* If there are no expansive nodes left, then we raise [Cannot_expand] *)
        raise Cannot_expand
      | Some dl_elt, None ->
        (* Trivial choice of a single expansive node *)
        t1, dl_elt
      | None, Some dl_elt -> t2, dl_elt
      | Some dl_elt1, Some dl_elt2 ->
        (* For 2 possible expansive nodes, we select the node with
             the maximum rank. *)
        let rank_of_dl_elt dl_elt =
          dl_elt |> Doubly_linked.Elt.get_value |> Elt.get_rank
        in
        if Int.compare (rank_of_dl_elt dl_elt1) (rank_of_dl_elt dl_elt2) > 0
        then t1, dl_elt1
        else t2, dl_elt2


    let expand ~ctx t1 t2 ~f =
      (* Determine the expansive list we're modifying. *)
      let t, dl_elt = get_expansive_view t1 t2 in
      let elt = Doubly_linked.Elt.get_value dl_elt in
      let former = Elt.get_former elt in
      let former_id = Former.id former in
      (* Determine the expansion. *)
      let vars, former' = Ctx.get_expansion ctx former_id in
      let former_id' = Former.id former' in
      (* Remove [dl_elt] from expansive, adding it to non-expansive. *)
      Doubly_linked.remove t.expansive dl_elt;
      Hashtbl.set t.elts ~key:(Former.id former) ~data:(Non_expansive elt);
      (* Add the expansion to either expansive or non-expansive (if it is primitive). *)
      let rank = Ctx.get_rank ctx former_id' in
      let desc =
        let elt = Elt.{ former = former'; rank } in
        if Ctx.has_abbrev ctx former_id'
        then Expansive (Doubly_linked.insert_first_elt t.expansive elt)
        else Non_expansive elt
      in
      Hashtbl.set t.elts ~key:(Former.id former') ~data:desc;
      (* Update the representative. *)
      if rank < rank_of_desc t.repr then t.repr <- desc;
      (* Iterate on decomposable positions of [former] *)
      let decomposable_positions =
        Ctx.get_decomposable_positions ctx former_id
      in
      let i = ref 0 in
      Former.iter former ~f:(fun t1 ->
          if Hash_set.mem decomposable_positions !i then f t1 vars.(!i);
          i := !i + 1)


    let iter2_exn ~ctx t1 t2 ~f =
      let rec loop () =
        try merge ~ctx t1 t2 ~f with
        | Cannot_merge ->
          if clash ~ctx t1 t2
          then raise Iter2
          else (
            (try expand ~ctx t1 t2 ~f with
            | Cannot_expand -> raise Iter2);
            loop ())
      in
      loop ()
  end

  type 'a ctx = 'a Productive_view.Ctx.t

  module Metadata = struct
    type 'a t =
      { non_productive_view : 'a Non_productive_view.t
      ; metadata : Metadata.t
      }
    [@@deriving sexp_of]

    let merge t1 t2 =
      { non_productive_view =
          Non_productive_view.merge
            t1.non_productive_view
            t2.non_productive_view
      ; metadata = Metadata.merge t1.metadata t2.metadata
      }
  end

  module Unifier = Unifier.Make (Productive_view) (Metadata)

  module Former_hash_key = struct
    type t = Unifier.Type.t Former.t [@@deriving sexp_of]

    let hash = Former.id
    let compare t1 t2 = Int.compare (hash t1) (hash t2)
  end

  let make_non_productive_view () = Hash_set.create (module Former_hash_key)

  let make_metadata metadata =
    Metadata.{ non_productive_view = make_non_productive_view (); metadata }


  let set_metadata t metadata' =
    let metadata = Unifier.Type.get_metadata t in
    Unifier.Type.set_metadata t { metadata with metadata = metadata' }


  let get_non_productive_view t =
    let metadata = Unifier.Type.get_metadata t in
    metadata.non_productive_view


  module Ctx = struct
    (* open Productive_view.Ctx *)

    type t =
      { abbreviations : (Int.t, Abbreviation.t, Int.comparator_witness) Map.t }

    let empty = { abbreviations = Map.empty (module Int) }

    let add t ~abbrev =
      { abbreviations =
          Map.set t.abbreviations ~key:(Abbreviation.id abbrev) ~data:abbrev
      }


    let has_abbrev t former_id = Map.mem t.abbreviations former_id

    exception Not_found

    let find_abbrev t former_id =
      match Map.find t.abbreviations former_id with
      | Some abbrev -> abbrev
      | None -> raise Not_found


    let get_productivity t former_id =
      find_abbrev t former_id |> Abbreviation.productivity


    let get_rank t former_id =
      match Map.find t.abbreviations former_id with
      | Some abbrev -> Abbreviation.rank abbrev
      | None -> 0
  end

  let make_flexible_var metadata =
    Unifier.Type.make_flexible_var (make_metadata metadata)


  let make_rigid_var rigid_var metadata =
    Unifier.Type.make_rigid_var rigid_var (make_metadata metadata)


  let make_former_productive ~ctx ~kind former metadata =
    let rank = Ctx.get_rank ctx (Former.id former) in
    let productive_view =
      let open Productive_view in
      let elt = Elt.{ former; rank } in
      singleton ~kind elt
    in
    Unifier.Type.make_former productive_view (make_metadata metadata)


  let make_former ~ctx former metadata =
    let former_id = Former.id former in
    if Ctx.has_abbrev ctx former_id
    then (
      (* [former] has an abbreviation and must be treated specially *)
      match Ctx.get_productivity ctx former_id with
      | Non_productive i ->
        (* [former] is non-productive => equivalent to [Former.nth former i] *)
        let type_ = Former.nth_exn former i in
        (* Add [former] to the non-productive views of [i] *)
        Non_productive_view.add (get_non_productive_view type_) former;
        set_metadata type_ metadata;
        type_
      | Productive _ ->
        make_former_productive ~ctx ~kind:`Expansive former metadata)
    else make_former_productive ~ctx ~kind:`Non_expansive former metadata


  let convert ~ctx ~metadata abbrev =
    let abbrev_vars, abbrev_former = Abbreviation.type_ abbrev in
    let copied : (Abbrev_type.t, Unifier.Type.t) Hashtbl.t =
      Hashtbl.create (module Abbrev_type)
    in
    (* Convert variables first (some may be phantoms) *)
    let uvars =
      List.map abbrev_vars ~f:(fun avar ->
          let uvar = make_flexible_var (metadata ()) in
          Hashtbl.set copied ~key:avar ~data:uvar;
          uvar)
      |> Array.of_list
    in
    (* Assume [atype] is acyclic *)
    let rec copy atype =
      try Hashtbl.find_exn copied atype with
      | Not_found_s _ ->
        let utype =
          match Abbrev_type.get_structure atype with
          | Abbrev_type.Var -> make_flexible_var (metadata ())
          | Abbrev_type.Former former ->
            make_former ~ctx (Former.map ~f:copy former) (metadata ())
        in
        Hashtbl.set copied ~key:atype ~data:utype;
        utype
    in
    uvars, Former.map ~f:copy abbrev_former


  let unify ~ctx ~metadata t1 t2 =
    Unifier.unify
      ~ctx:
        { abbreviations = Ctx.(ctx.abbreviations)
        ; productive_convert = convert ~ctx ~metadata
        }
      t1
      t2
end
