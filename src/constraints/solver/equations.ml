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
  let init n ~f = { array = Option_array.init_some n ~f }
  let get t i = Option_array.get t.array i
  let get_some_exn t i = Option_array.get_some_exn t.array i

  let set t i x =
    ensure_capacity t i;
    Option_array.set t.array i x


  let set_some t i x =
    ensure_capacity t i;
    Option_array.set_some t.array i x
end

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
    let init n ~f = ref (Vector (Option_vec.init n ~f))

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

    type 'a ref = int

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
    type 'a t = 'a link Store.ref

    and 'a link =
      | Root of int * 'a
      | Link of 'a t

    type 'a store = 'a t Store.t

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
          let desc = f desc1 desc2 in
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
  end
end




module Make (Former : Type_former.S) (Metadata : Unifier.Metadata) = struct
  module Unifier = Unifier.Make (Former) (Metadata)
  module U = Unifier

  module Equation = struct
    type t = U.Type.t * U.Type.t

    let ( =. ) t1 t2 = t1, t2
  end

  (* TODO: Improve efficiency! Use a persistent union-find implementation *)

  (* An equation environment [t] consists of a set of equations
       in solved form. 
    *)
  type t = Equation.t list

  exception Inconsistent

  (* [add_equation t (t1 =. t2)] adds the solved form of the equation
       [t1 =. t2] to the environment [t]. 
       
       Warning! Assumes [t1 =. t2] is not cyclic
    *)
  let add_equation t (type1, type2) =
    (* TODO: Implement fold2_exn for Former. Removes reference side-effect. *)
    let t = ref t in
    let rec loop t1 t2 =
      match U.Type.get_structure t1, U.Type.get_structure t2 with
      | Var { flexibility = Rigid }, _ | _, Var { flexibility = Rigid } ->
        t := (t1, t2) :: !t
      | Former former1, Former former2 ->
        Former.iter2_exn ~f:loop former1 former2
      | _, _ -> ()
    in
    (try loop type1 type2 with
    (* If we add an equation that implies [bool = int], then the equation is
         inconsistent *)
    | Former.Iter2 -> raise Inconsistent);
    !t


  let equivalence_class t type_ =
    List.fold_left t ~init:[ type_ ] ~f:(fun acc (type1, type2) ->
        if phys_equal type1 type_
        then type1 :: acc
        else if phys_equal type2 type_
        then type2 :: acc
        else acc)


  (* This is actually horrifying, but its a prototype ;) *)
  let rec equivalent t type1 type2 : bool =
    let class1 = equivalence_class t type1
    and class2 = equivalence_class t type2 in
    (* Again, relying on exceptions for control flow. Unncessary, use fold! *)
    let equiv t1 t2 : bool =
      if phys_equal t1 t2
      then true
      else
        let exception Not_equiv in
        try
          (match U.Type.get_structure t1, U.Type.get_structure t2 with
          | Var _, Var _ -> if not (phys_equal t1 t2) then raise Not_equiv
          | Former former1, Former former2 ->
            Former.iter2_exn
              ~f:(fun t1 t2 -> if not (equivalent t t1 t2) then raise Not_equiv)
              former1
              former2
          | _, _ -> raise Not_equiv);
          true
        with
        | Former.Iter2 | Not_equiv -> false
    in
    List.exists ~f:(List.mem ~equal:phys_equal class1) class2
    || List.exists
         ~f:(fun t1 -> List.exists ~f:(fun t2 -> equiv t1 t2) class1)
         class2
end