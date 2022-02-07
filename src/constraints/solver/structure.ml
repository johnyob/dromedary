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
include Structure_intf

module Rigid_var = struct
  module T = struct
    type t = int [@@deriving sexp_of, compare]
  end

  include T
  include Comparator.Make (T)

  let make =
    let next = ref 0 in
    fun () -> post_incr next


  let hash t = t
end

module Of_former (Former : Type_former.S) = struct
  module Metadata = struct
    type 'a t = unit [@@deriving sexp_of]

    let empty () = ()
    let merge () () = ()
  end

  include Former

  type ctx = unit
  type 'a expansive = unit

  exception Cannot_merge

  let merge ~expansive:() ~ctx:() ~equate (t1, ()) (t2, ()) =
    (try Former.iter2_exn t1 t2 ~f:equate with
    | Former.Iter2 -> raise Cannot_merge);
    t1
end

module First_order (Structure : S) = struct
  include Structure

  type 'a t =
    | Var
    | Structure of 'a Structure.t
  [@@deriving sexp_of]

  let iter t ~f =
    match t with
    | Var -> ()
    | Structure structure -> Structure.iter structure ~f


  let map t ~f =
    match t with
    | Var -> Var
    | Structure structure -> Structure (Structure.map structure ~f)


  let fold t ~f ~init =
    match t with
    | Var -> init
    | Structure structure -> Structure.fold structure ~f ~init


  let merge ~expansive ~ctx ~equate (desc1, metadata1) (desc2, metadata2) =
    match desc1, desc2 with
    | Var, desc | desc, Var -> desc
    | Structure desc1, Structure desc2 ->
      Structure
        (Structure.merge
           ~expansive
           ~ctx
           ~equate
           (desc1, metadata1)
           (desc2, metadata2))
end

module Scoped_abbreviations
    (Structure : S)
    (Id : Identifiable with type 'a t := 'a Structure.t) =
struct
  module Abbrev = struct
    module Type = struct
      type t = desc ref [@@deriving sexp_of]

      and desc =
        { id : int
        ; structure : structure
        }

      and structure =
        | Var
        | Structure of t Structure.t

      let make =
        let id = ref 0 in
        fun structure -> ref { id = post_incr id; structure }


      let structure t = !t.structure
      let id t = !t.id
      let compare t1 t2 = Int.compare (id t1) (id t2)
      let hash = id
    end

    module Scope = struct
      type t = int [@@deriving sexp_of]

      let outermost_scope = 0
      let max = max
    end

    type t =
      { structure : Type.t Structure.t
      ; type_ : Type.t
      ; scope : Scope.t
      }
    [@@deriving sexp_of]

    let expand { structure; type_; _ } = structure, type_
    let scope t = t.scope

    module Ctx = struct
      type nonrec t = (Int.t, t, Int.comparator_witness) Map.t

      let empty : t = Map.empty (module Int)

      let add (t : t) ~abbrev:(structure, type_) ~scope : t =
        Map.set t ~key:(Id.id structure) ~data:{ structure; type_; scope }


      let find t structure = Map.find t (Id.id structure)
    end
  end

  include Structure

  module Metadata = struct
    type 'a t =
      { mutable scope : Abbrev.Scope.t
      ; super_ : 'a Metadata.t
      }
    [@@deriving sexp_of]

    let empty () =
      { scope = Abbrev.Scope.outermost_scope; super_ = Metadata.empty () }


    let merge t1 t2 =
      { scope = Abbrev.Scope.max t1.scope t2.scope
      ; super_ = Metadata.merge t1.super_ t2.super_
      }


    let scope t = t.scope
    let update_scope t scope = if t.scope < scope then t.scope <- scope
    let super_ t = t.super_
  end

  type ctx = Abbrev.Ctx.t * Structure.ctx

  let actx = fst
  let sctx = snd
  let make t = t

  type 'a expansive =
    { make_structure : 'a Structure.t -> 'a
    ; make_var : unit -> 'a
    ; super_ : 'a Structure.expansive
    }

  let convert_abbrev ~expansive abbrev =
    let abbrev_structure, abbrev_type = Abbrev.expand abbrev in
    let copied : (Abbrev.Type.t, _) Hashtbl.t =
      Hashtbl.create (module Abbrev.Type)
    in
    (* Assume [abbrev_type] is acyclic *)
    let rec copy type_ =
      try Hashtbl.find_exn copied type_ with
      | Not_found_s _ ->
        let new_type =
          match Abbrev.Type.structure type_ with
          | Var -> expansive.make_var ()
          | Structure structure ->
            expansive.make_structure (Structure.map ~f:copy structure)
        in
        Hashtbl.set copied ~key:type_ ~data:new_type;
        new_type
    in
    let abbrev_structure = Structure.map ~f:copy abbrev_structure in
    let abbrev_type = copy abbrev_type in
    abbrev_structure, abbrev_type


  let repr t = t

  let merge ~expansive ~(ctx : ctx) ~equate (t1, metadata1) (t2, metadata2) =
    let ( === ) t1 t2 = Id.id t1 = Id.id t2 in
    let ( =~ ) t1 t2 =
      Structure.merge
        ~expansive:expansive.super_
        ~ctx:(sctx ctx)
        ~equate
        (t1, Metadata.super_ metadata1)
        (t2, Metadata.super_ metadata2)
    in
    let ( =~- ) a t =
      let a' = expansive.make_structure t in
      equate a a'
    in
    let expand_with_abbrev t ~abbrev =
      (* Expand the abbreviation of [t] *)
      let abbrev_structure, abbrev_type = convert_abbrev ~expansive abbrev in
      (* Equate the variables and children of [t]. *)
      ignore (t =~ abbrev_structure : _ Structure.t);
      abbrev_type
    in
    if t1 === t2
    then t1 =~ t2
    else (
      match Abbrev.Ctx.find (actx ctx) t1 with
      | None ->
        (match Abbrev.Ctx.find (actx ctx) t2 with
        | None -> raise Cannot_merge
        | Some abbrev ->
          (* Expand [t2] to [t2'], and merge [t2'] and [t1]. *)
          let t2' = expand_with_abbrev t2 ~abbrev in
          (* Merge [t2'] and [t1]. *)
          t2' =~- t1;
          (* Update scope *)
          Metadata.update_scope metadata1 (Abbrev.scope abbrev);
          t1)
      | Some abbrev ->
        (* Expand [t2] to [t2'], and merge [t2'] and [t1]. *)
        let t1' = expand_with_abbrev t1 ~abbrev in
        (* Merge [t2'] and [t1]. *)
        t1' =~- t2;
        (* Update scope *)
        Metadata.update_scope metadata2 (Abbrev.scope abbrev);
        t2)
end

module Rigid_structure (Structure : S) = struct
  include Structure

  type 'a t =
    | Rigid_var of Rigid_var.t
    | Structure of 'a Structure.t
  [@@deriving sexp_of]

  let iter t ~f =
    match t with
    | Rigid_var _ -> ()
    | Structure structure -> Structure.iter structure ~f


  let map t ~f =
    match t with
    | Rigid_var rigid_var -> Rigid_var rigid_var
    | Structure structure -> Structure (Structure.map structure ~f)


  let fold t ~f ~init =
    match t with
    | Rigid_var _ -> init
    | Structure structure -> Structure.fold structure ~f ~init


  let merge ~expansive ~ctx ~equate (desc1, metadata1) (desc2, metadata2) =
    match desc1, desc2 with
    | Rigid_var rigid_var1, Rigid_var rigid_var2
      when Rigid_var.compare rigid_var1 rigid_var2 = 0 -> Rigid_var rigid_var1
    | Structure desc1, Structure desc2 ->
      Structure
        (Structure.merge
           ~expansive
           ~ctx
           ~equate
           (desc1, metadata1)
           (desc2, metadata2))
    | _ -> raise Cannot_merge
end

module Rigid_identifiable (S : S) (Id : Identifiable with type 'a t = 'a S.t) =
struct
  module Rigid_structure = Rigid_structure (S)
  include Rigid_structure

  let id t =
    match t with
    | Rigid_var var -> 2 * Rigid_var.hash var
    | Structure structure -> (2 * Id.id structure) + 1
end