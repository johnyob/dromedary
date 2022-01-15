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

(* This module implements a the unifier. *)

open! Import

(* Include module types and type definitions from the [_intf] file. *)

include Unifier_intf

module Make (Former : Type_former.S) (Metadata : Metadata) :
  S with type 'a former := 'a Former.t and type metadata := Metadata.t = struct
  (* Unification involves unification types, using the union-find 
     data structure. 
     
     These are referred to as "graphical types" in the dissertation. 
     
     While are formalization doesn't exactly match our implementation, 
     the notion provides useful insight. 
  *)

  module Abbreviations = Abbreviations.Make (Former)
  module A = Abbreviations

  module Non_productive_view = struct
    type 'a t = 'a Hash_set.t [@@deriving sexp_of]

    let iter = Hash_set.iter
    let fold t ~init ~f = Hash_set.fold t ~init ~f:(fun acc x -> f x acc)
    let repr t = Hash_set.find t ~f:(Fn.const true)
    let empty ~hash_key = Hash_set.create hash_key
    let add t x = Hash_set.add t x
    let merge t1 t2 = Hash_set.union t1 t2
  end

  module Productive_view = struct
    module Elt = struct
      type 'a t =
        { value : 'a
        ; rank : int
        }
      [@@deriving sexp_of]

      let value t = t.value
      let rank t = t.rank
    end

    type 'a t =
      { mutable repr : 'a desc
      ; expansive : 'a Elt.t Doubly_linked.t
      ; elts : (int, 'a desc) Hashtbl.t
      }
    [@@deriving sexp_of]

    and 'a desc =
      | Non_expansive of 'a Elt.t
      | Expansive of 'a Elt.t Doubly_linked.Elt.t

    let elt_of_desc desc =
      match desc with
      | Non_expansive elt -> elt
      | Expansive dl_elt -> Doubly_linked.Elt.get_value dl_elt


    let singleton ~hash ~kind elt =
      let expansive = Doubly_linked.empty () in
      let desc =
        match kind with
        | `Non_expansive -> Non_expansive elt
        | `Expansive -> Expansive (Doubly_linked.insert_first_elt expansive elt)
      in
      let elts = Hashtbl.create (module Int) in
      Hashtbl.set elts ~key:(hash (Elt.value elt)) ~data:desc;
      { repr = desc; expansive; elts }


    let iter t ~f =
      Hashtbl.iter t.elts ~f:(fun desc -> elt_of_desc desc |> Elt.value |> f)


    let fold (type a b) (t : a t) ~(init : b) ~(f : a -> b -> b) : b =
      Hashtbl.fold t.elts ~init ~f:(fun ~key:_ ~data:desc acc ->
          f (elt_of_desc desc |> Elt.value) acc)


    let repr t = t.repr |> elt_of_desc |> Elt.value
  end

  (* See: https://github.com/janestreet/base/issues/121 *)
  let post_incr r =
    let result = !r in
    Int.incr r;
    result


  module Rigid_var = struct
    type t = int [@@deriving compare, sexp_of]

    let make =
      let next = ref 0 in
      fun () -> post_incr next


    let id t = t
    let hash t = t
  end

  module Type = struct
    (* A graphical type consists of a [Union_find] node,
       allowing reasoning w/ multi-equations of nodes. *)

    type t = desc Union_find.t [@@deriving sexp_of]

    (* Graphical type node descriptors contain information related to the 
       node that dominates the multi-equation.

       Each node contains a global unique identifier [id]. 
       This is allocated on [fresh]. On [union], an arbitrary 
       identifier is used from the 2 arguments. 
       
       We use this identifier [id] for a total ordering on nodes, often 
       used for efficient datastructures such as [Hashtbl] or [Hash_set]. 

       Each descriptor stores the node structure [structure].
       It is either a variable or a type former (with graph type node 
       children). 
       
       Each node also maintains some mutable metadata [metadata], whose
       purpose is not related to unification. 
       
       Note: the only operation performed by the unifier wrt metadata is
       the merging of metadata on unification. No further traversals / updates
       are implemented here. 
    *)
    and desc =
      { id : int
      ; mutable structure : structure
      ; mutable non_productive_view : non_productive_view
      ; mutable metadata : Metadata.t
      }
    [@@deriving sexp_of]

    (* Graphical type node structures are either variables or type
       formers. 
       
       A variable denotes it's flexibility, using {!flexibility}.
       This is required for unification under a mixed prefix. 
    *)
    and structure =
      | Flexible_var
      | Rigid_var of Rigid_var.t
      | Former of productive_view
    [@@deriving sexp_of]

    and non_productive_view = t Former.t Non_productive_view.t
    [@@deriving sexp_of]

    and productive_view = t Former.t Productive_view.t [@@deriving sexp_of]

    module View_hash_key = struct
      type type_ = t [@@deriving sexp_of]
      type t = type_ Former.t [@@deriving sexp_of]

      let hash t = Former.hash t
      let compare t1 t2 = Int.compare (hash t1) (hash t2)
    end

    (* [id t] returns the unique identifier of the type [t]. *)
    let id t = (Union_find.find t).id
    let get_non_productive_view t = (Union_find.find t).non_productive_view

    let set_non_productive_view t non_productive_view =
      (Union_find.find t).non_productive_view <- non_productive_view


    (* [get_structure t] returns the structure of [t]. *)
    let get_structure t = (Union_find.find t).structure

    (* [set_structure t structure] sets the structure of [t] to [structure]. *)
    let set_structure t structure = (Union_find.find t).structure <- structure

    (* [get_metadata t] returns the metadata of [t]. *)
    let get_metadata t = (Union_find.find t).metadata

    (* [set_metadata t metadata] sets the metadata of [t] to [metadata]. *)
    let set_metadata t metadata = (Union_find.find t).metadata <- metadata

    (* [compare t1 t2] computes the ordering of [t1, t2],
       based on their unique identifiers. *)

    let compare t1 t2 = Int.compare (id t1) (id t2)

    (* [hash t] computes the hash of the graphical type [t]. 
       Based on it's integer field: id. *)

    let hash t = Hashtbl.hash (id t)

    (* [make structure metadata] returns a fresh type w/ structure [structure] and
     metadata [metadata]. *)
    let make =
      let id = ref 0 in
      fun structure metadata ->
        Union_find.make
          { id = post_incr id
          ; structure
          ; metadata
          ; non_productive_view =
              Non_productive_view.empty ~hash_key:(module View_hash_key)
          }


    (* [make_var flexibility metadata] returns a fresh variable 
     with flexibility [flexibility], and metadata [metadata]. *)
    let make_flexible_var metadata = make Flexible_var metadata
    let make_rigid_var rigid_var metadata = make (Rigid_var rigid_var) metadata

    (* [make_former ctx former metadata] returns a fresh former
       with former [former] and metadata [metadata] under abbreviation context [ctx].  *)
    let make_former ~ctx former metadata =
      if A.Ctx.has_abbrev ctx former
      then (
        (* [former] has an abbreviation and must be treated specially *)
        match A.Ctx.get_productivity ctx former with
        | Non_productive i ->
          (* [former] is non-productive => equivalent to [Former.nth former i] *)
          let type_ = Former.nth former i in
          (* Add [former] to the non-productive views of [i] *)
          Non_productive_view.add (get_non_productive_view type_) former;
          set_metadata type_ metadata;
          type_
        | Productive ->
          (* TODO: Remove code duplication! *)
          let productive_view =
            let open Productive_view in
            let elt =
              Elt.{ value = former; rank = A.Ctx.get_rank ctx former }
            in
            singleton ~hash:Former.hash ~kind:`Expansive elt
          in
          make (Former productive_view) metadata)
      else (
        (* [former] has no abbreviation => it is a primitive, thus
           may be treated as "non-expansive" *)
        let productive_view =
          let open Productive_view in
          let elt = Elt.{ value = former; rank = A.Ctx.get_rank ctx former } in
          singleton ~hash:Former.hash ~kind:`Non_expansive elt
        in
        make (Former productive_view) metadata)


    module To_dot = struct
      type state =
        { mutable id : int
        ; buffer : Buffer.t
        }

      let basic_shape ~label ~metadata () : string =
        let label = String.escaped label in
        let metadata = String.escaped metadata in
        [%string
          {|[style=filled, tooltip = "%{metadata}", shape = oval, label = "%{label}"];|}]


      let structure_to_string structure : string =
        match structure with
        | Flexible_var -> [%string "*"]
        | Rigid_var rigid_var -> Sexp.to_string (Rigid_var.sexp_of_t rigid_var)
        | Former productive_view ->
          Former.sexp_of_t
            (fun _ -> Atom "")
            (Productive_view.repr productive_view)
          |> Sexp.to_string_hum


      let metadata_to_string metadata : string =
        metadata |> Metadata.sexp_of_t |> Sexp.to_string_hum


      let register state t : string =
        let id = [%string "%{state.id#Int}"] in
        Buffer.add_string state.buffer id;
        Buffer.add_char state.buffer ' ';
        Buffer.add_string
          state.buffer
          (basic_shape
             ~label:(structure_to_string (get_structure t))
             ~metadata:(metadata_to_string (get_metadata t))
             ());
        Buffer.add_char state.buffer '\n';
        state.id <- state.id + 1;
        id


      let arrow state ~from ~to_ =
        Buffer.add_string state.buffer [%string "%{from} -> %{to_};\n"]


      let follow_type state t =
        let table = Hashtbl.create (module Int) in
        let rec loop t =
          match Hashtbl.find table (id t) with
          | Some me -> me
          | None ->
            let me = register state t in
            Hashtbl.set table ~key:(id t) ~data:me;
            (match get_structure t with
            | Flexible_var | Rigid_var _ -> ()
            | Former productive_view ->
              Former.iter (Productive_view.repr productive_view) ~f:(fun t ->
                  let from = loop t in
                  arrow state ~from ~to_:me));
            me
        in
        loop t
    end

    let to_dot t =
      let open To_dot in
      let state = { id = 0; buffer = Buffer.create 2042 } in
      let _root = follow_type state t in
      let contents = Buffer.contents state.buffer in
      [%string "digraph {\n %{contents}}"]


    exception Cannot_flexize of t

    let flexize_desc desc_src desc_dst =
      { id = desc_dst.id
      ; structure = desc_dst.structure
      ; non_productive_view =
          Non_productive_view.merge
            desc_src.non_productive_view
            desc_dst.non_productive_view
      ; metadata = Metadata.merge desc_src.metadata desc_dst.metadata
      }


    let flexize ~src ~dst =
      match get_structure src with
      | Rigid_var _ -> Union_find.union src dst ~f:flexize_desc
      | _ -> raise (Cannot_flexize src)
  end

  open Type

  (* We now extend [Productive_view] for additional functions revelent to the 
     unification of productive views. 
     
     These functions will be specialized to [Type.productive_view]. 
  *)

  module Productive_view_ = struct
    open Productive_view

    let find t key = Hashtbl.find_exn t.elts key |> elt_of_desc |> Elt.value

    (* let former_of_desc desc = elt_of_desc desc |> Elt.value *)
    let rank_of_desc desc = elt_of_desc desc |> Elt.rank

    exception Cannot_merge

    let iter_decomposable_positions ~ctx former1 former2 ~f =
      assert (Former.hash former1 = Former.hash former2);
      let decomposable_positions =
        A.Ctx.get_decomposable_positions ctx former1
      in
      List.iter decomposable_positions ~f:(fun i ->
          let type1 = Former.nth former1 i
          and type2 = Former.nth former2 i in
          f type1 type2)


    let merge ~ctx t1 t2 ~f =
      (* Determine whether there is a common former in [t1] or [t2] *)
      let former_key =
        Hash_set.inter
          (Hash_set.of_hashtbl_keys t1.elts)
          (Hash_set.of_hashtbl_keys t2.elts)
        |> Hash_set.find ~f:(Fn.const true)
      in
      match former_key with
      | None -> raise Cannot_merge
      | Some former_key ->
        (* Compute the merged former descriptor *)
        let former =
          let former1 = find t1 former_key
          and former2 = find t2 former_key in
          iter_decomposable_positions ~ctx former1 former2 ~f;
          former1
        in
        (* Now determine the structure of the former descriptor,
            we assert that they have the same descriptor structure *)
        let desc =
          match Hashtbl.find_exn t1.elts former_key with
          | Non_expansive elt -> Non_expansive Elt.{ elt with value = former }
          | Expansive dl_elt ->
            let elt = Doubly_linked.Elt.get_value dl_elt in
            Doubly_linked.Elt.set_value dl_elt Elt.{ elt with value = former };
            Expansive dl_elt
        in
        Hashtbl.set t1.elts ~key:former_key ~data:desc;
        (* Merge fields (picking t1 as the preferred view on duplicate) *)
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
        (* Merge the representative *)
        let repr =
          Comparable.min
            (fun desc1 desc2 ->
              Int.compare (rank_of_desc desc1) (rank_of_desc desc2))
            t1.repr
            t2.repr
        in
        { repr; expansive; elts }


    let clash ~ctx t1 t2 =
      let formers t =
        t.elts
        |> Hashtbl.data
        |> List.map ~f:(fun desc -> elt_of_desc desc |> Elt.value)
      in
      let formers1 = formers t1 in
      let formers2 = formers t2 in
      List.cartesian_product formers1 formers2
      |> List.exists ~f:(fun (former1, former2) ->
             A.Ctx.clash ctx former1 former2)


    exception Cannot_expand

    let expand ~ctx ~metadata t1 t2 ~f =
      (* Determine the expansive list we're modifying *)
      let t, dl_elt =
        (* Get the minimum expandable nodes *)
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
            dl_elt |> Doubly_linked.Elt.get_value |> Elt.rank
          in
          if Int.compare (rank_of_dl_elt dl_elt1) (rank_of_dl_elt dl_elt2) > 0
          then t1, dl_elt1
          else t2, dl_elt2
      in
      let elt = Doubly_linked.Elt.get_value dl_elt in
      let former = Elt.value elt in
      (* Determine the expansion of the former *)
      let avars, aformer = A.Ctx.get_expansion ctx former in
      (* Convert the expansion type to a unifier type *)
      let uvars, uformer =
        let copied : (A.Type.t, Type.t) Hashtbl.t =
          Hashtbl.create (module A.Type)
        in
        (* Convert variables first (some may be phantoms) *)
        let uvars =
          List.map avars ~f:(fun avar ->
              let uvar = make_flexible_var (metadata ()) in
              Hashtbl.set copied ~key:avar ~data:uvar;
              uvar)
        in
        (* Assume [atype] is acyclic *)
        let rec copy atype =
          try Hashtbl.find_exn copied atype with
          | Not_found_s _ ->
            let utype =
              match A.Type.get_structure atype with
              | A.Type.Var -> make_flexible_var (metadata ())
              | A.Type.Former former ->
                make_former ~ctx (Former.map ~f:copy former) (metadata ())
            in
            Hashtbl.set copied ~key:atype ~data:utype;
            utype
        in
        uvars, Former.map ~f:copy aformer
      in
      (* Remove [dl_elt] from expansive, add to non-expansive. *)
      Doubly_linked.remove t.expansive dl_elt;
      Hashtbl.set t.elts ~key:(Former.hash former) ~data:(Non_expansive elt);
      (* Add new former to either expansive or primitives (non-expansive) *)
      let elt' = Elt.{ value = uformer; rank = A.Ctx.get_rank ctx uformer } in
      let desc' =
        if A.Ctx.has_abbrev ctx uformer
        then Expansive (Doubly_linked.insert_first_elt t.expansive elt')
        else Non_expansive elt'
      in
      Hashtbl.set t.elts ~key:(Former.hash uformer) ~data:desc';
      (* Update representive, expanded former may be new minima. *)
      if elt'.rank < rank_of_desc t.repr then t.repr <- desc';
      (* Iterate on decomposable positions of [former], unifying 
         vars of [former] and [uvars] *)
      let decomposable_positions =
        A.Ctx.get_decomposable_positions ctx former
      in
      List.iter decomposable_positions ~f:(fun i ->
          let type1 = Former.nth former i
          and type2 = List.nth_exn uvars i in
          f type1 type2)
  end

  exception Cannot_unify_rigid_variable
  exception Clash

  (* [unify_exn] unifies two graphical types. No exception handling is 
     performed here. This is an internal function.
     
     Possible exceptions include:
     - [Former.Iter2], raised when executing Former.iter2 in {unify_form}.
     - [Unify_rigid], raised when incorrectly unifying a rigid variable.

     See {!unify}. 
  *)

  let rec unify_exn ~ctx ~metadata t1 t2 =
    Union_find.union ~f:(unify_desc ~ctx ~metadata) t1 t2


  (* [unify_desc desc1 desc2] unifies the descriptors of the graph types
     (of multi-equations). *)

  and unify_desc ~ctx ~metadata desc1 desc2 =
    { id = desc1.id
    ; structure = unify_structure ~ctx ~metadata desc1.structure desc2.structure
    ; metadata = Metadata.merge desc1.metadata desc2.metadata
    ; non_productive_view =
        Non_productive_view.merge
          desc1.non_productive_view
          desc2.non_productive_view
    }


  (* [unify_structure structure1 structure2] unifies two graph type node
     structures. We handle rigid variables here. *)

  and unify_structure ~ctx ~metadata structure1 structure2 =
    match structure1, structure2 with
    (* Unification of variables
    
       Unification is permitted between distinct variables only if 
       both variables are *not* rigid.
  
       In the case of 2 rigid variable, we raise [Cannot_unify_rigid_variable].

       We may unify a rigid variable with itself. However, this case does 
       not arise here since [Union_find.union] checks physical equality 
       before before [unify_structure] is executed. 
    *)
    | Rigid_var rigid_var1, Rigid_var rigid_var2 ->
      if Rigid_var.compare rigid_var1 rigid_var2 = 0
      then Rigid_var rigid_var1
      else raise Cannot_unify_rigid_variable
    | Rigid_var rigid_var, Flexible_var | Flexible_var, Rigid_var rigid_var ->
      Rigid_var rigid_var
    | Flexible_var, Flexible_var -> Flexible_var
    (* Unification of variables (leaves) and type formers (internal nodes)
    
       We may unify a flexible variable with a type former, yielding
       the same type former. 

       Note that no propagation of metadata is performed. This is required
       by external modules. See {!generalization.ml}. 
    *)
    | Flexible_var, Former productive_view
    | Former productive_view, Flexible_var -> Former productive_view
    (* Unification between a rigid variable and a type former is not 
       permitted. We raise [Unify_rigid]. *)
    | Rigid_var _, Former _ | Former _, Rigid_var _ ->
      raise Cannot_unify_rigid_variable
    (* Unification between type formers (via productive views).
    
       We may unify type formers recursively. See {!unify_former}. 
    *)
    | Former productive_view1, Former productive_view2 ->
      Former
        (unify_productive_views
           ~ctx
           ~metadata
           productive_view1
           productive_view2)


  (* [unify_former former1 former2] recursively unifies 2 type formers.

     Here we use our internal unification function [unify_exn],
     to allow exception propagation to the top-level call. *)

  and unify_productive_views ~ctx ~metadata productive_view1 productive_view2 =
    let rec loop () =
      (* First attempt to merge the views *)
      try
        Productive_view_.merge
          ~ctx
          productive_view1
          productive_view2
          ~f:(unify_exn ~ctx ~metadata)
      with
      | Productive_view_.Cannot_merge ->
        (* If cannot merge, then determine whether a clash occurs *)
        if Productive_view_.clash ~ctx productive_view1 productive_view2
        then raise Clash
        else (
          (* We now expand, and then recurse  *)
          (try
             (* Caml.Format.printf "Expanding\n"; *)
             Productive_view_.expand
               ~ctx
               ~metadata
               productive_view1
               productive_view2
               ~f:(unify_exn ~ctx ~metadata)
           with
          (* Caml.Format.printf "Expanded!\n" *)
          | Productive_view_.Cannot_expand ->
            (* Caml.Format.printf "Cannot expand!\n"; *)
            raise Clash);
          loop ())
    in
    loop ()


  exception Unify of Type.t * Type.t

  let unify ~ctx ~metadata t1 t2 =
    try unify_exn ~ctx ~metadata t1 t2 with
    | Clash | Cannot_unify_rigid_variable -> raise (Unify (t1, t2))


  exception Cycle of Type.t

  (* [occurs_check t] detects whether there is a cycle in 
     the graphical type [t]. 
      
     If a cycle is detected, [Cycle t] is raised. 
  *)
  let occurs_check =
    (* Hash table records the variables that are grey ([false])
       or black ([true]). *)
    let table = Hashtbl.create (module Type) in
    (* Recursive loop that traverses the graph, checking 
       for cycles. *)
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
        | Flexible_var | Rigid_var _ ->
          (* A variable is a leaf. Hence no traversal is
             required, so simply mark as visited. *)
          Hashtbl.set table ~key:t ~data:true
        | Former productive_view ->
          (* Mark this node as grey. *)
          Hashtbl.set table ~key:t ~data:false;
          (* Visit children *)
          Productive_view.iter productive_view ~f:(Former.iter ~f:loop);
          (* Mark this variable as black. *)
          Hashtbl.set table ~key:t ~data:true)
    in
    loop


  (* [fold_acyclic type_ ~var ~form] will perform a bottom-up fold
     over the (assumed) acyclic graph defined by the type [type_]. *)

  let fold_acyclic
      (type a)
      type_
      ~(flexible_var : Type.t -> a)
      ~(rigid_var : Rigid_var.t -> Type.t -> a)
      ~(former : a Former.t -> a)
      : a
    =
    (* Hash table records whether node has been visited, and 
      it's computed value. *)
    let visited : (Type.t, a) Hashtbl.t = Hashtbl.create (module Type) in
    (* Recursive loop, folding over the graph *)
    let rec loop type_ =
      try Hashtbl.find_exn visited type_ with
      | Not_found_s _ ->
        let result =
          match get_structure type_ with
          | Flexible_var -> flexible_var type_
          | Rigid_var a -> rigid_var a type_
          | Former productive_view ->
            former (Former.map ~f:loop (Productive_view.repr productive_view))
        in
        (* We assume we can set [type_] in [visited] *after* traversing
          it's children, since the graph is acyclic. *)
        Hashtbl.set visited ~key:type_ ~data:result;
        result
    in
    loop type_


  let fold_cyclic
      (type a)
      type_
      ~(flexible_var : Type.t -> a)
      ~(rigid_var : Rigid_var.t -> Type.t -> a)
      ~(former : a Former.t -> a)
      ~(mu : Type.t -> a -> a)
      : a
    =
    (* Hash table records the variables that are grey ([false])
       or black ([true]). *)
    let table = Hashtbl.create (module Type) in
    (* Recursive loop that traverses the graph. *)
    let rec loop t =
      match get_structure t with
      | Flexible_var ->
        Hashtbl.set table ~key:t ~data:true;
        flexible_var t
      | Rigid_var a -> 
        Hashtbl.set table ~key:t ~data:true;
        rigid_var a t
      | Former productive_view ->
        if Hashtbl.mem table t
        then (
          (* Mark this node as black *)
          Hashtbl.set table ~key:t ~data:true;
          flexible_var t)
        else (
          (* Mark this node as grey. *)
          Hashtbl.set table ~key:t ~data:false;
          (* Visit children *)
          let result =
            former (Former.map ~f:loop (Productive_view.repr productive_view))
          in
          let status = Hashtbl.find_exn table t in
          Hashtbl.remove table t;
          if status then mu t result else result)
    in
    loop type_
end
