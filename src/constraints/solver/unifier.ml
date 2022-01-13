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

(* Implementation of doubly linked. Would use [Core]'s impl, 
     but doesn't provide merge *)
module Doubly_linked = struct
  module Elt = struct
    type 'a t =
      { mutable value : 'a
      ; mutable next : 'a t option
      ; mutable prev : 'a t option
      }
    [@@deriving sexp_of]

    let value t = t.value

    let unlink t =
      t.next <- None;
      t.prev <- None


    let of_value value = { value; next = None; prev = None }
    let set_value t value = t.value <- value
  end

  type 'a t =
    { mutable first : 'a Elt.t option
    ; mutable last : 'a Elt.t option
    }
  [@@deriving sexp_of]

  let empty () = { first = None; last = None }

  let first t = t.first
  let last t = t.last
  let first_elt t = Option.(first t >>| Elt.value)
  let last_elt t = Option.(last t >>| Elt.value)

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
      Some (Elt.value first)


  let insert_first t elt =
    Elt.(elt.next <- t.first);
    (match t.first with
    | Some first -> first.prev <- Some elt
    | None -> ());
    t.first <- Some elt


  let insert_last t elt =
    Elt.(elt.prev <- t.last);
    (match t.last with
    | Some last -> last.next <- Some elt
    | None -> ());
    t.last <- Some elt


  let insert_first_elt t x =
    let elt = Elt.of_value x in
    insert_first t elt;
    elt


  let insert_last_elt t x =
    let elt = Elt.{ prev = t.last; next = None; value = x } in
    insert_last t elt;
    elt


  let append t1 t2 =
    (match t1.last with
    | Some last -> last.next <- t2.first
    | None -> t1.first <- t2.first);
    (match t2.first with
    | Some first -> first.prev <- t1.last
    | None -> t2.first <- t1.last);
    t2.first <- t1.first;
    t1.last <- t2.last;
    t1


  let merge t1 t2 ~compare =
    let rec loop t1 t2 =
      match t1.first, t2.first with
      | None, _ -> t2
      | _, None -> t1
      | Some first1, Some first2 ->
        if compare (Elt.value first1) (Elt.value first2) < 0
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
end

module Make (Former : Type_former.S) (Metadata : Metadata) :
  S with type 'a former := 'a Former.t and type metadata := Metadata.t = struct
  (* Unification involves unification types, using the union-find 
     data structure. 
     
     These are referred to as "graphical types" in the dissertation. 
     
     While are formalization doesn't exactly match our implementation, 
     the notion provides useful insight. 
  *)

  module Abbreviations = Abbreviations.Make (Former)

  module Type = struct
    (* There are two kinds of variables [Flexible] and [Rigid]. 
    
       A [Flexible] variable can be unified with other variables and types. 
       A [Rigid] (in general) cannot be unified. 
    *)
    type flexibility =
      | Flexible
      | Rigid
    [@@deriving sexp_of, eq]

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
      | Var of { mutable flexibility : flexibility }
      | Former of productive_view
    [@@deriving sexp_of]

    and non_productive_view = t Former.t Hash_set.t [@@deriving sexp_of]

    and productive_view =
      { formers : (int, former_desc) Hashtbl.t
      ; primitive : t Former.t Doubly_linked.t
      ; expansive : productive_view_elt Doubly_linked.t
      ; non_expansive : productive_view_elt Doubly_linked.t
      }
    [@@deriving sexp_of]

    and productive_view_elt =
      { rank : int
      ; former : t Former.t
      }
    [@@deriving sexp_of]

    and former_desc =
      | Primitive of t Former.t Doubly_linked.Elt.t
      | Non_expansive of productive_view_elt Doubly_linked.Elt.t
      | Expansive of productive_view_elt Doubly_linked.Elt.t

    module type View = sig
      (** aliases for types. *)
      type type_ := t

      (** [t] encodes the type of the view. It's structure is abstract, providing potentially 
          more efficient implementations in the future. *)
      type t [@@deriving sexp_of]

      val iter : t -> f:(type_ Former.t -> unit) -> unit
      val fold : t -> init:'a -> f:('a -> type_ Former.t -> 'a) -> 'a
    end

    module Non_productive_view = struct
      type type_ = t [@@deriving sexp_of]
      type t = non_productive_view [@@deriving sexp_of]

      let iter = Hash_set.iter
      let fold = Hash_set.fold

      module Former_hash_key = struct
        type t = type_ Former.t [@@deriving sexp_of]

        let hash t = Former.hash t
        let compare t1 t2 = Int.compare (hash t1) (hash t2)
      end

      let empty () = Hash_set.create (module Former_hash_key)
      let merge t1 t2 = Hash_set.union t1 t2
      let add t former = Hash_set.add t former
    end

    (* [id t] returns the unique identifier of the type [t]. *)
    let id t = (Union_find.find t).id
    let get_non_productive_view t = (Union_find.find t).non_productive_view

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

    (* See: https://github.com/janestreet/base/issues/121 *)
    let post_incr r =
      let result = !r in
      Int.incr r;
      result


    (* [make structure metadata] returns a fresh type w/ structure [structure] and
     metadata [metadata]. *)
    let make =
      let id = ref 0 in
      fun structure metadata ->
        Union_find.make
          { id = post_incr id
          ; structure
          ; metadata
          ; non_productive_view = Non_productive_view.empty ()
          }


    (* [make_var flexibility metadata] returns a fresh variable 
     with flexibility [flexibility], and metadata [metadata]. *)
    let make_var flexibility metadata = make (Var { flexibility }) metadata

    module Productive_view = struct
      type type_ = t
      type t = productive_view [@@deriving sexp_of]

      let former_of_former_desc desc =
        match desc with
        | Primitive elt -> Doubly_linked.Elt.value elt
        | Non_expansive elt | Expansive elt ->
          (Doubly_linked.Elt.value elt).former

      let empty () = 
        { formers = Hashtbl.create (module Int)
        ; primitive = Doubly_linked.empty ()
        ; expansive = Doubly_linked.empty ()
        ; non_expansive = Doubly_linked.empty ()
        }

      let add_former t abbrev_env former = 
        match Abbreviations.get_productivity abbrev_env former with
        | Primitive ->
          let desc = Primitive (Doubly_linked.insert_first_elt t.primitive former) in
          Hashtbl.set t.formers ~key:(Former.hash former) ~data:desc
        | Productive ->
          let view_elt = 
            { former; rank = Abbreviations.get_rank abbrev_env former }
          in
          let desc = Expansive (Doubly_linked.insert_first_elt t.expansive view_elt) in
          Hashtbl.set t.formers ~key:(Former.hash former) ~data:desc
        | _ -> assert false


      let iter t ~f =
        Hashtbl.iter t.formers ~f:(fun desc -> f (former_of_former_desc desc))


      let fold t ~init ~f =
        Hashtbl.fold t.formers ~init ~f:(fun ~key:_ ~data:desc accum ->
            f accum (former_of_former_desc desc))


      let repr t =
        (* Primitives are of rank 0 => minima *)
        match Doubly_linked.first_elt t.primitive with
        | Some former -> former
        | None ->
          (* Minimum of expansive < non-expansive. *)
          (match Doubly_linked.first_elt t.expansive with
          | Some elt -> elt.former
          | None ->
            (match Doubly_linked.first_elt t.non_expansive with
            | Some elt -> elt.former
            | None -> assert false))


      let of_former abbrev_env former =
        let t = empty () in
        add_former t abbrev_env former;
        t


      (* [make_former former metadata] returns a fresh type former
     with metadata [metadata]. *)
      let make_former abbrev_env former metadata =
        match Abbreviations.get_productivity abbrev_env former with
        | Non_productive i ->
          let type_ = Former.get former i in
          (* Add the former to the non-productive view, return the variable
         that it is equivalent too. *)
          Non_productive_view.add (get_non_productive_view type_) former;
          type_
        | _ ->
          (* [Productive_view.of_former] assumes that [former] is productive 
         in the environment [abbrev_env]. *)
          make (Former (of_former abbrev_env former)) metadata


      let find_former t i =
        Hashtbl.find_exn t.formers i |> former_of_former_desc


      let formers t =
        Hashtbl.data t.formers |> List.map ~f:former_of_former_desc


      exception Cannot_merge

      (* [common_former t1 t2] returns the "first" former hash in both [t1] and [t2]. *)
      let common_former t1 t2 =
        Hash_set.inter
          (Hash_set.of_hashtbl_keys t1.formers)
          (Hash_set.of_hashtbl_keys t2.formers)
        |> Hash_set.find ~f:(Fn.const true)


      (* Assumes [can_merge t1 t2] is true *)
      let merge t1 t2 ~f =
        let common_former = common_former t1 t2 in
        match common_former with
        | None -> raise Cannot_merge
        | Some i ->
          let new_former = f (find_former t1 i) (find_former t2 i) in
          let compare desc1 desc2 = Int.compare desc1.rank desc2.rank in
          let primitive = Doubly_linked.append t1.primitive t2.primitive in
          let non_expansive =
            Doubly_linked.merge t1.non_expansive t2.non_expansive ~compare
          in
          let expansive =
            Doubly_linked.merge t1.expansive t2.expansive ~compare
          in
          let formers =
            Hashtbl.merge t1.formers t2.formers ~f:(fun ~key:_ data ->
                match data with
                | `Left desc | `Right desc | `Both (desc, _) -> Some desc)
          in
          Hashtbl.set
            formers
            ~key:i
            ~data:
              (match Hashtbl.find_exn formers i with
              | Primitive elt ->
                Doubly_linked.Elt.set_value elt new_former;
                Primitive elt
              | Non_expansive desc_elt ->
                let desc = Doubly_linked.Elt.value desc_elt in
                Doubly_linked.Elt.set_value
                  desc_elt
                  { desc with former = new_former };
                Non_expansive desc_elt
              | Expansive desc_elt ->
                let desc = Doubly_linked.Elt.value desc_elt in
                Doubly_linked.Elt.set_value
                  desc_elt
                  { desc with former = new_former };
                Expansive desc_elt);
          { formers; primitive; non_expansive; expansive }


      let clash abbrev_env t1 t2 =
        let formers1 = formers t1 in
        let formers2 = formers t2 in
        List.cartesian_product formers1 formers2
        |> List.exists ~f:(fun (former1, former2) ->
               Abbreviations.clash abbrev_env former1 former2)


      exception Cannot_expand

      let expand abbrev_env expansive_metadata t1 t2 ~f : unit =
        let desc1 = Doubly_linked.first t1.expansive in
        let desc2 = Doubly_linked.first t2.expansive in
        let expand t desc_elt =
          let desc = Doubly_linked.Elt.value desc_elt in
          (* Determine abbreviation *)
          let vars, former =
            Abbreviations.get_expansion abbrev_env desc.former
            |> Option.value_exn ~here:[%here]
          in
          (* Convert abbreviation type to unifier type *)
          let vars, former =
            let copied : (Abbreviations.Type.t, type_) Hashtbl.t =
              Hashtbl.create (module Abbreviations.Type)
            in
            let rec copy atype =
              let utype = make_var Flexible (expansive_metadata ()) in
              Hashtbl.set copied ~key:atype ~data:utype;
              let structure =
                match Abbreviations.Type.get_structure atype with
                | Abbreviations.Type.Var -> Var { flexibility = Flexible }
                | Abbreviations.Type.Former former ->
                  Former (of_former abbrev_env (Former.map ~f:copy former))
              in
              set_structure utype structure;
              utype
            in
            let former = Former.map ~f:copy former in
            List.map ~f:(Hashtbl.find_exn copied) vars, former
          in
          (* Remove desc from expansive, add to non-expansive *)
          Doubly_linked.remove t.expansive desc_elt;
          Doubly_linked.insert_first t.non_expansive desc_elt;
          (* Add new desc to primitive or expansive *)
          (match Abbreviations.get_productivity abbrev_env former with
          | Primitive ->
            ignore
              (Doubly_linked.insert_first_elt t.primitive former
                : _ Doubly_linked.Elt.t)
          | Productive ->
            ignore
              (Doubly_linked.insert_first_elt
                 t.expansive
                 { former; rank = Abbreviations.get_rank abbrev_env former }
                : _ Doubly_linked.Elt.t)
          | _ -> assert false);
          (* Iterate on variables *)
          let decomposable_positions =
            Abbreviations.get_decomposable_positions abbrev_env desc.former
            |> Option.value_exn ~here:[%here]
          in
          List.iter decomposable_positions ~f:(fun i ->
              f (Former.get desc.former i) (List.nth_exn vars i))
        in
        match desc1, desc2 with
        | Some desc1, Some desc2 ->
          if (Doubly_linked.Elt.value desc1).rank
             < (Doubly_linked.Elt.value desc2).rank
          then expand t2 desc2
          else expand t1 desc1
        | Some desc, _ -> expand t1 desc
        | _, Some desc -> expand t2 desc
        | None, None -> raise Cannot_expand
    end

    let make_former = Productive_view.make_former

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
        | Var { flexibility = Flexible } -> [%string "*"]
        | Var { flexibility = Rigid } -> [%string "!"]
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
            | Var _ -> ()
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
  end

  open Type

  (* TODO: Fix signatures, so we have [U.Type.make_var, etc] *)
  let make_var = make_var
  let make_former = make_former

  exception Cannot_unify_rigid_variable
  exception Clash

  (* [unify_exn] unifies two graphical types. No exception handling is 
     performed here. This is an internal function.
     
     Possible exceptions include:
     - [Former.Iter2], raised when executing Former.iter2 in {unify_form}.
     - [Unify_rigid], raised when incorrectly unifying a rigid variable.

     See {!unify}. 
  *)

  let rec unify_exn abbrev_env expansive_metadata t1 t2 =
    Union_find.union ~f:(unify_desc abbrev_env expansive_metadata) t1 t2


  (* [unify_desc desc1 desc2] unifies the descriptors of the graph types
     (of multi-equations). *)

  and unify_desc abbrev_env expansive_metadata desc1 desc2 =
    { id = desc1.id
    ; structure =
        unify_structure
          abbrev_env
          expansive_metadata
          desc1.structure
          desc2.structure
    ; metadata = Metadata.merge desc1.metadata desc2.metadata
    ; non_productive_view =
        Non_productive_view.merge
          desc1.non_productive_view
          desc2.non_productive_view
    }


  (* [unify_structure structure1 structure2] unifies two graph type node
     structures. We handle rigid variables here. *)

  and unify_structure abbrev_env expansive_metadata structure1 structure2 =
    match structure1, structure2 with
    (* Unification of variables
    
       Unification is permitted between distinct variables only if 
       both variables are *not* rigid.
  
       In the case of 2 rigid variable, we raise [Cannot_unify_rigid_variable].

       We may unify a rigid variable with itself. However, this case does 
       not arise here since [Union_find.union] checks physical equality 
       before before [unify_structure] is executed. 
    *)
    | Var { flexibility = Rigid }, Var { flexibility = Rigid } ->
      raise Cannot_unify_rigid_variable
    | Var { flexibility = Rigid }, Var { flexibility = Flexible }
    | Var { flexibility = Flexible }, Var { flexibility = Rigid } ->
      Var { flexibility = Rigid }
    | Var { flexibility = Flexible }, Var { flexibility = Flexible } ->
      Var { flexibility = Flexible }
    (* Unification of variables (leaves) and type formers (internal nodes)
    
       We may unify a flexible variable with a type former, yielding
       the same type former. 

       Note that no propagation of metadata is performed. This is required
       by external modules. See {!generalization.ml}. 
    *)
    | Var { flexibility = Flexible }, Former productive_view
    (* Unification between a rigid variable and a type former is not 
       permitted. We raise [Unify_rigid]. *)
    | Former productive_view, Var { flexibility = Flexible } ->
      Former productive_view
    | Var { flexibility = Rigid }, Former _
    | Former _, Var { flexibility = Rigid } -> raise Cannot_unify_rigid_variable
    (* Unification between type formers (via productive views).
    
       We may unify type formers recursively. See {!unify_former}. 
    *)
    | Former productive_view1, Former productive_view2 ->
      Former
        (unify_productive_views
           abbrev_env
           expansive_metadata
           productive_view1
           productive_view2)


  (* [unify_former former1 former2] recursively unifies 2 type formers.

     Here we use our internal unification function [unify_exn],
     to allow exception propagation to the top-level call. *)

  and unify_productive_views
      abbrev_env
      expansive_metadata
      productive_view1
      productive_view2
    =
    let rec loop () =
      (* First attempt to merge the views *)
      try
        Productive_view.merge
          productive_view1
          productive_view2
          ~f:(fun former1 former2 ->
            (* Assert hash of former1 = hash of former2 *)
            let decomposable_positions =
              Abbreviations.get_decomposable_positions abbrev_env former1
              |> Option.value_exn ~here:[%here]
            in
            List.iter decomposable_positions ~f:(fun i ->
                let type1 = Former.get former1 i
                and type2 = Former.get former2 i in
                unify_exn abbrev_env expansive_metadata type1 type2);
            former1)
      with
      | Productive_view.Cannot_merge ->
        (* If cannot merge, then determine whether a clash occurs *)
        if Productive_view.clash abbrev_env productive_view1 productive_view2
        then raise Clash
        else
          (* We now expand, and then recurse  *)
          Productive_view.expand
            abbrev_env
            expansive_metadata
            productive_view1
            productive_view2
            ~f:(unify_exn abbrev_env expansive_metadata);
        loop ()
    in
    loop ()


  (* Former.iter2_exn ~f:unify_exn former1 former2;
    former1 *)

  exception Unify of Type.t * Type.t

  let unify abbrev_env expansive_metadata t1 t2 =
    try unify_exn abbrev_env expansive_metadata t1 t2 with
    | Former.Iter2 | Cannot_unify_rigid_variable -> raise (Unify (t1, t2))


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
        | Var _ ->
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
      ~(var : Type.t -> a)
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
          | Var _ -> var type_
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
      ~(var : Type.t -> a)
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
      | Var _ ->
        Hashtbl.set table ~key:t ~data:true;
        var t
      | Former productive_view ->
        if Hashtbl.mem table t
        then (
          (* Mark this node as black *)
          Hashtbl.set table ~key:t ~data:true;
          var t)
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
