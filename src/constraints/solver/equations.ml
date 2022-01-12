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
include Equations_intf

module Option_vec = struct
  let growth_rate = 2

  type 'a t = { mutable array : 'a Option_array.t }

  let rec new_length length i =
    if i < length then length else new_length (length * growth_rate) i


  let ensure_capacity t i =
    let array = t.array in
    let length = Option_array.length array in
    if i >= length
    then (
      let array' = Option_array.create ~len:(new_length length i) in
      Option_array.blit ~src:array ~src_pos:0 ~dst:array' ~dst_pos:0 ~len:length;
      t.array <- array')


  let make ?len:(n = 0) () = { array = Option_array.create ~len:n }
  (* let init n ~f = { array = Option_array.init_some n ~f } *)
  let get t i = Option_array.get t.array i
  let get_some_exn t i = Option_array.get_some_exn t.array i

  let set t i x =
    ensure_capacity t i;
    Option_array.set t.array i x


  let set_some t i x =
    ensure_capacity t i;
    Option_array.set_some t.array i x
end

(* TODO: Move to a separate library *)

module Persistent = struct
  (* An implementation of the persistent union-find algorithm.

     Uses [Option_vec] for a persistent implementation of a vector. 
     [Vec] is used to for a persistent [Store].    
  *)

  module Vec = struct
    type 'a t = 'a desc ref

    and 'a desc =
      | Vector of 'a Option_vec.t
          (** [Vectpr arr] is a persistent array w/ values from vector [arr] *)
      | Difference of int * 'a option * 'a t
          (** [Difference (i, x, t)] is a persistent array w/ the values of [t]
              but w/ index [i] storing [x]. *)

    let make ~len = ref (Vector (Option_vec.make ~len ()))
    (* let init n ~f = ref (Vector (Option_vec.init n ~f)) *)

    let rec reroot_ t ~k =
      match !t with
      | Vector vec -> k vec
      | Difference (i, x, t') ->
        reroot_ t' ~k:(fun vec ->
            let x' = Option_vec.get vec i in
            Option_vec.set vec i x;
            t := Vector vec;
            t' := Difference (i, x', t);
            k vec)


    let reroot t = reroot_ t ~k:Fn.id
    let get t i = Option_vec.get_some_exn (reroot t) i
  
    let set t i x =
      let vec = reroot t in
      let x' = Option_vec.get vec i in
      Option_vec.set_some vec i x;
      let t' = ref (Vector vec) in
      t := Difference (i, x', t');
      t'
  end

  module Store = struct
    type 'a t =
      { vector : 'a Vec.t
      ; next : int
      }

    type 'a ref = int [@@deriving sexp_of]

    exception Invalid_ref

    let bounds_check t i = if i >= t.next then raise Invalid_ref

    let get t ref =
      bounds_check t ref;
      Vec.get t.vector ref


    let set t ref x =
      bounds_check t ref;
      { t with vector = Vec.set t.vector ref x }


    let make () = { vector = Vec.make ~len:512; next = 0 }

    let make_ref t x =
      let ref = t.next in
      { next = t.next + 1; vector = Vec.set t.vector ref x }, ref


    let phys_equal t ref1 ref2 =
      bounds_check t ref1;
      bounds_check t ref2;
      ref1 = ref2
  end

  module Union_find = struct
    type 'a t = 'a link Store.ref [@@deriving sexp_of]

    and 'a link =
      | Root of int * 'a
      | Link of 'a t

    type 'a store = 'a link Store.t

    let make_store () = Store.make ()
    let make store desc = Store.make_ref store (Root (0, desc))

    let rec root store t =
      match Store.get store t with
      | Root _ -> store, t
      | Link t' ->
        let store, root' = root store t' in
        if not (Store.phys_equal store t' root')
        then (
          let store = Store.set store t (Store.get store t') in
          store, root')
        else store, root'


    let rec find store t =
      match Store.get store t with
      | Root (_, desc) -> store, desc
      | Link t' ->
        (match Store.get store t' with
        | Root (_, desc) -> store, desc
        | Link _ ->
          let store, root = root store t in
          find store root)


    let rec set store t desc =
      match Store.get store t with
      | Root (rank, _) -> Store.set store t (Root (rank, desc))
      | Link t' ->
        (match Store.get store t' with
        | Root (rank, _) -> Store.set store t (Root (rank, desc))
        | Link _ ->
          let store, root = root store t in
          set store root desc)


    let link store t1 t2 ~f =
      if Store.phys_equal store t1 t2
      then store
      else (
        match Store.get store t1, Store.get store t2 with
        | Root (rank1, desc1), Root (rank2, desc2) ->
          let store, desc = f store desc1 desc2 in
          if rank1 > rank2
          then (
            let store = Store.set store t2 (Link t1) in
            let store = Store.set store t1 (Root (rank1, desc)) in
            store)
          else (
            let rank = if rank1 < rank2 then rank1 else rank1 + 1 in
            let store = Store.set store t1 (Link t2) in
            let store = Store.set store t2 (Root (rank, desc)) in
            store)
        | _ -> assert false)


    let union store t1 t2 ~f =
      let store, root1 = root store t1 in
      let store, root2 = root store t2 in
      link store root1 root2 ~f


    let is_equivalent store t1 t2 =
      if t1 = t2
      then store, true
      else (
        let store, root1 = root store t1 in
        let store, root2 = root store t2 in
        store, root1 = root2)
  end

  module Unifier (Former : Type_former.S) (Metadata : Unifier.Metadata) = struct
    module Type = struct
      type t = desc Union_find.t [@@deriving sexp_of]

      and desc =
        { id : int
        ; metadata : Metadata.t
        ; structure : structure
        }

      and structure =
        | Var
        | Former of t Former.t

      let id store t =
        let store, desc = Union_find.find store t in
        store, desc.id


      let get_structure store t =
        let store, desc = Union_find.find store t in
        store, desc.structure


      let set_structure store t structure =
        let store, desc = Union_find.find store t in
        Union_find.set store t { desc with structure }


      let get_metadata store t =
        let store, desc = Union_find.find store t in
        store, desc.metadata


      let set_metadata store t metadata =
        let store, desc = Union_find.find store t in
        Union_find.set store t { desc with metadata }


      let compare store t1 t2 =
        let store, id1 = id store t1 in
        let store, id2 = id store t2 in
        store, Int.compare id1 id2


      let hash store t =
        let store, id = id store t in
        store, Hashtbl.hash id
    end

    open Type

    (* See: https://github.com/janestreet/base/issues/121 *)
    let post_incr r =
      let result = !r in
      Int.incr r;
      result


    type store = Type.desc Union_find.store

    let make_store () = Union_find.make_store ()

    let make =
      let id = ref 0 in
      fun store structure metadata ->
        Union_find.make store { id = post_incr id; metadata; structure }


    let rec unify_exn store t1 t2 = Union_find.union store ~f:unify_desc t1 t2

    and unify_desc store desc1 desc2 =
      let store, structure =
        unify_structure store desc1.structure desc2.structure
      in
      ( store
      , { id = desc1.id
        ; metadata = Metadata.merge desc1.metadata desc2.metadata
        ; structure
        } )


    and unify_structure store structure1 structure2 =
      match structure1, structure2 with
      | Var, structure | structure, Var -> store, structure
      | Former former1, Former former2 ->
        let store, former = unify_former store former1 former2 in
        store, Former former


    and unify_former store former1 former2 =
      let store =
        Former.fold2_exn
          ~init:store
          ~f:(fun t1 t2 store -> unify_exn store t1 t2)
          former1
          former2
      in
      store, former1


    exception Unify of Type.t * Type.t

    let unify store t1 t2 =
      try unify_exn store t1 t2 with
      | Former.Fold2 -> raise (Unify (t1, t2))


    exception Cycle of Type.t

    let occurs_check store t =
      (* To make use of efficient datastructures, we ensure that [store] is 
         locally mutable *)
      let store = ref store in
      (* Hash table records whether the types are grey ([false])
         or black [true]. *)
      let table =
        Hashtbl.create
          (module struct
            type t = Type.t [@@deriving sexp_of]

            let compare t1 t2 =
              let store', result = Type.compare !store t1 t2 in
              store := store';
              result


            let hash t =
              let store', result = Type.hash !store t in
              store := store';
              result
          end)
      in
      (* Wrapper for [get_structure] that uses the locally mutable [store]. *)
      let get_structure t =
        let store', structure = Type.get_structure !store t in
        store := store';
        structure
        (* Recursive loop that traverse the graphical type, checking
         for cycles. *)
      in
      let rec loop t =
        try
          (* We raise an exception [Not_found_s] instead of using
             an option, since it is more efficient.
          *)
          let visited = Hashtbl.find_exn table t in
          (* A cycle has occurred is the variable is grey. *)
          if not visited then raise (Cycle t)
        with
        | Not_found_s _ ->
          (match get_structure t with
          | Var ->
            (* A variable is a leaf. Hence no traversal is
               required, so simply mark as visited. *)
            Hashtbl.set table ~key:t ~data:true
          | Former former ->
            (* Mark this node as grey. *)
            Hashtbl.set table ~key:t ~data:false;
            (* Visit children *)
            Former.iter ~f:loop former;
            (* Mark this variable as black. *)
            Hashtbl.set table ~key:t ~data:true)
      in
      loop t;
      !store


    let is_equivalent store t1 t2 =
      let exception Not_equiv in
      let rec loop store t1 t2 =
        (* Determine whether [t1] and [t2] are members of the same equivalence class. *)
        let store, result = Union_find.is_equivalent store t1 t2 in
        if result
        then raise Not_equiv
        else (
          (* If they are not members of the same equivalence class, then they may still be 
             structurally equivalent. *)
          let store, structure1 = get_structure store t1 in
          let store, structure2 = get_structure store t2 in
          match structure1, structure2 with
          | Former former1, Former former2 ->
            (* If the formers are not structurally equal, then we raise [Fold2]. 
               If they are structurally equal, we recurse to it's children to determine
               whether they are structurally equal.  
            *)
            let store =
              Former.fold2_exn
                former1
                former2
                ~init:store
                ~f:(fun t1 t2 store -> loop store t1 t2)
            in
            (* An error has not been raise => proof of equivalence, hence both nodes should
               be members of the same equivalence class (which is what we do)
            *)
            let store =
              Union_find.union store t1 t2 ~f:(fun store desc1 desc2 ->
                  ( store
                  , { id = desc1.id
                    ; structure = desc1.structure
                    ; metadata = Metadata.merge desc1.metadata desc2.metadata
                    } ))
            in
            store
          | _, _ ->
            (* If they are not members of the same equivalence class and they have no matching 
               structure, then they are not structurally equivalent. *)
            store)
      in
      try
        let store = loop store t1 t2 in
        store, true
      with
      | Former.Fold2 | Not_equiv -> store, false
  end
end

module Make
    (Former : Type_former.S)
    (Metadata : Unifier.Metadata)
    (Rigid_metadata : Unifier.Metadata) =
struct
  module Rigid_unifier = Persistent.Unifier (Former) (Rigid_metadata)
  module R = Rigid_unifier

  type state = { store : R.store }

  let make_state () = { store = R.make_store () }

  module Rigid_type = struct
    type t = R.Type.t [@@deriving sexp_of]

    type structure = R.Type.structure =
      | Var
      | Former of t Former.t

    let id state t =
      let store, id = R.Type.id state.store t in
      { store }, id


    let get_structure state t =
      let store, structure = R.Type.get_structure state.store t in
      { store }, structure


    let set_structure state t structure =
      let store = R.Type.set_structure state.store t structure in
      { store }


    let get_metadata state t =
      let store, metadata = R.Type.get_metadata state.store t in
      { store }, metadata


    let set_metadata state t metadata =
      let store = R.Type.set_metadata state.store t metadata in
      { store }
  end

  let make_rigid state structure metadata =
    let store, t = R.make state.store structure metadata in
    { store }, t


  let make_rigid_var state metadata = make_rigid state Var metadata

  let make_rigid_former state former metadata =
    make_rigid state (Former former) metadata


  module Ambivalence = struct
    type t = R.Type.t list [@@deriving sexp_of]

    (* TODO: Maybe use difference lists? *)
    let merge t1 t2 = t1 @ t2
  end

  (* Instantiate the unifier *)

  module Metadata = struct
    type t = Ambivalence.t * Metadata.t [@@deriving sexp_of]

    let merge (ambivalence1, metadata1) (ambivalence2, metadata2) =
      ( Ambivalence.merge ambivalence1 ambivalence2
      , Metadata.merge metadata1 metadata2 )
  end

  module Unifier = Unifier.Make (Former) (Metadata)
  module U = Unifier

  module Equation = struct
    type t = Rigid_type.t * Rigid_type.t [@@deriving sexp_of]

    (* TODO: Add invariants + occurs check *)
    let ( =. ) t1 t2 = t1, t2
  end

  exception Inconsistent

  let add_equation state (type1, type2) =
    try
      let store = R.unify state.store type1 type2 in
      let store = R.occurs_check store type1 in
      { store }
    with
    | R.Unify _ | R.Cycle _ -> raise Inconsistent


  let get_ambivalence t = fst (U.Type.get_metadata t)
  let get_metadata t = snd (U.Type.get_metadata t)

  let set_ambivalence t ambivalence =
    U.Type.set_metadata t (ambivalence, get_metadata t)


  let consistency_check state types =
    (* For efficiency purposes, we will make use of a locally mutable store *)
    let store = ref state.store in
    (* Similarly, we will use an exception [Inconsistent_type] to quickly return from a nested traversal. *)
    let exception Inconsistent_type in
    (* Hash set records whether we've visited a given nopde, prevents cyclic execution of [loop]. *)
    let visited : U.Type.t Hash_set.t = Hash_set.create (module U.Type) in
    (* Alias for [R.Type.get_structure] that wraps the locally mutable store. *)
    let get_structure t =
      let store', structure = R.Type.get_structure !store t in
      store := store';
      structure
    in
    let rec loop type_ =
      if not (Hash_set.mem visited type_)
      then (
        (* Mark as visited first. This is required for types containing cycles. *)
        Hash_set.add visited type_;
        match get_ambivalence type_ with
        | [] ->
          (* A node with no ambivalence is trivially consistent under any equational context *)
          ()
        | ambivalent :: ambivalence ->
          (* We first must determine whether the ambivalent types are equal. *)
          (* Warning: This logic relies on the implementation of [Persistent_vec],
             but when determining the equivalent node, we must use the "youngest" reference
             to the node in the resultant ambivalent. *)
          let ambivalent =
            List.fold_left
              ambivalence
              ~init:ambivalent
              ~f:(fun ambivalent rigid_type ->
                let store', result =
                  R.is_equivalent !store ambivalent rigid_type
                in
                if not result then raise Inconsistent_type;
                store := store';
                min ambivalent rigid_type)
          in
          set_ambivalence type_ [ ambivalent ];
          (* We now determine whether the structure of the type is structurally equal to the ambivalent
             type. *)
          (match U.Type.get_structure type_, get_structure ambivalent with
          | U.Type.Var, _ ->
            (* For a variable, and a consistent ambivalent, this is also trivially consistent. *)
            (* This is due to the fact that variables are flexible. *)
            ()
          | U.Type.Former former, Rigid_type.Former former' ->
            (* Here we propagate ambivalence to the subparts of the type, providing efficiency 
               consistency. *)
            (* We determine whether the formers of the ambivalent and type match, if so, then
               we propagate the ambivalence, thus ensuring that true consistency is checked when we
               visit the node. 
            *)
            Former.iter2_exn former former' ~f:(fun type_ rigid_type ->
                set_ambivalence type_ (rigid_type :: get_ambivalence type_));
            (* We now recurse, which will ensure that we check the consistency of the propagated 
               ambivalence. *)
            Former.iter former ~f:loop
          | _, _ -> raise Inconsistent_type))
    in
    try
      List.iter ~f:loop types;
      { store = !store }, true
    with
    | Inconsistent_type | Former.Fold2 -> state, false
end
