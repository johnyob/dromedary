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

  module Rigid_var = struct
    module T = struct
      type t = int [@@deriving sexp_of, compare]
    end

    include T
    include Comparator.Make (T)

    let id t = t

    let make =
      let id = ref 0 in
      fun () -> post_incr id


    let hash = id
  end

  module Rigid_type = struct
    module T = struct
      type t = desc ref [@@deriving sexp_of]

      and desc =
        { id : int
        ; structure : structure
        }

      and structure =
        | Var of Rigid_var.t
        | Former of t Former.t

      let id t = !t.id
      let compare t1 t2 = Int.compare (id t1) (id t2)
      let hash t = id t
    end

    include T

    let get_structure t = !t.structure

    let make =
      let id = ref 0 in
      fun structure -> ref { id = post_incr id; structure }


    let make_var rigid_var = make (Var rigid_var)
    let make_former former = make (Former former)

    let to_type ~make_var ~make_former rigid_type =
      let copied : (T.t, _) Hashtbl.t = Hashtbl.create (module T) in
      let rec copy rigid_type =
        try Hashtbl.find_exn copied rigid_type with
        | Not_found_s _ ->
          let result =
            match get_structure rigid_type with
            | Var rigid_var -> make_var rigid_var
            | Former former -> make_former (Former.map ~f:copy former)
          in
          Hashtbl.set copied ~key:rigid_type ~data:result;
          result
      in
      copy rigid_type
  end

  module Equations = struct
    module Scope = struct
      type t = int [@@deriving sexp_of]

      let max = max
      let min = min
      let outermost_scope = 0
    end

    module Ctx = struct
      type t =
        { equations :
            ( Rigid_var.t
            , Scope.t * Rigid_type.t
            , Rigid_var.comparator_witness )
            Map.t
        }

      let empty = { equations = Map.empty (module Rigid_var) }

      exception Inconsistent

      let get_equation t rigid_var = Map.find t.equations rigid_var

      let rec add_equation t rigid_var type1 metadata =
        match Map.find t.equations rigid_var with
        | Some (_, type2) -> add_equations t type1 type2 metadata
        | None ->
          { equations =
              Map.set t.equations ~key:rigid_var ~data:(metadata, type1)
          }


      and add_equations t type1 type2 metadata =
        let open Rigid_type in
        match get_structure type1, get_structure type2 with
        | Var rigid_var, _ -> add_equation t rigid_var type2 metadata
        | _, Var rigid_var -> add_equation t rigid_var type1 metadata
        | Former former1, Former former2 ->
          Former.fold2_exn former1 former2 ~init:t ~f:(fun type1 type2 t ->
              add_equations t type1 type2 metadata)


      let add t type1 type2 metadata =
        try add_equations t type1 type2 metadata with
        | Former.Fold2 -> raise Inconsistent
    end
  end

  module Rigid_view = struct
    type 'a t =
      { mutable former : ('a Former.t * Equations.Scope.t) option
      ; elts : (Rigid_var.t, desc) Hashtbl.t
      ; repr : Rigid_var.t
      }
    [@@deriving sexp_of]

    and desc =
      { is_expansive : bool
      ; scope : Equations.Scope.t
      }

    let repr t = t.repr

    let iter t ~f =
      Option.iter t.former ~f:(fun (former, _) -> Former.iter former ~f)


    let fold t ~init ~f =
      Option.fold t.former ~init ~f:(fun init (former, _) ->
          Former.fold former ~init ~f)


    let singleton rigid_var =
      let elts = Hashtbl.create (module Rigid_var) in
      Hashtbl.set
        elts
        ~key:rigid_var
        ~data:{ is_expansive = true; scope = Equations.Scope.outermost_scope };
      { former = None; elts; repr = rigid_var }
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
      ; mutable scope : Equations.Scope.t
      ; mutable metadata : Metadata.t
      }
    [@@deriving sexp_of]

    (* Graphical type node structures are either variables or type
       formers. *)
    and structure =
      | Flexible_var
      | Rigid_var of rigid_view
      | Former of t Former.t
    [@@deriving sexp_of]

    and rigid_view = t Rigid_view.t

    (* [id t] returns the unique identifier of the type [t]. *)
    let id t = (Union_find.find t).id

    (* [get_structure t] returns the structure of [t]. *)
    let get_structure t = (Union_find.find t).structure

    (* [set_structure t structure] sets the structure of [t] to [structure]. *)
    let set_structure t structure = (Union_find.find t).structure <- structure
    let get_scope t = (Union_find.find t).scope
    let set_scope t scope = (Union_find.find t).scope <- scope

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
          ; scope = Equations.Scope.outermost_scope
          }


    (* [make_flexible_var metadata] returns a fresh variable 
       with flexibility [flexibility], and metadata [metadata]. *)
    let make_flexible_var metadata = make Flexible_var metadata

    let make_rigid_var rigid_var metadata =
      make (Rigid_var (Rigid_view.singleton rigid_var)) metadata


    (* [make_former former metadata] returns a fresh former
       with former [former] and metadata [metadata]. *)
    let make_former former metadata = make (Former former) metadata

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
        | Rigid_var rigid_view -> Int.to_string (Rigid_view.repr rigid_view)
        | Former former ->
          Former.sexp_of_t (fun _ -> Atom "") former |> Sexp.to_string_hum


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
            | Former former ->
              Former.iter former ~f:(fun t ->
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
      ; metadata = Metadata.merge desc_src.metadata desc_dst.metadata
      ; scope = Equations.Scope.max desc_src.scope desc_dst.scope
      }


    let flexize ~src ~dst =
      match get_structure src with
      | Rigid_var _ -> Union_find.union src dst ~f:flexize_desc
      | _ -> raise (Cannot_flexize src)
  end

  open Type

  type 'a expansive =
    { value : 'a
    ; make_var : Rigid_var.t -> Type.t
    ; make_former : Type.t Former.t -> Type.t
    }

  module Rigid_view_ = struct
    open Rigid_view

    exception Cannot_merge
    exception Cannot_expand
    exception Clash

    let merge_former t1 t2 =
      match t1.former, t2.former with
      | None, former | former, None -> former
      | Some (former, scope1), Some (_, scope2) ->
        Some (former, Equations.Scope.min scope1 scope2)


    let merge_elts t1 t2 =
      let elts =
        Hashtbl.merge t1.elts t2.elts ~f:(fun ~key:_ data ->
            match data with
            | `Left desc | `Right desc -> Some desc
            | `Both (desc1, desc2) ->
              Some
                { is_expansive = desc1.is_expansive && desc2.is_expansive
                ; scope = Equations.Scope.min desc1.scope desc2.scope
                })
      in
      elts


    let rigid_vars t = Hash_set.of_hashtbl_keys t.elts
    let former t = t.former
    let scope t rigid_var = (Hashtbl.find_exn t.elts rigid_var).scope

    (* [merge t1 t2 ~f] attempts to merge [t1] and [t2]. 
       If we merge on [former], then we iterate over it w/ [f]. 
       
       Returns the newly created view and scope. *)
    let merge t1 t2 ~f =
      let merge () =
        (* Merge former *)
        let former = merge_former t1 t2 in
        (* Merge the elements *)
        let elts = merge_elts t1 t2 in
        (* Pick arbitrary representative *)
        let repr = t1.repr in
        { repr; elts; former }
      in
      match Option.both t1.former t2.former with
      | None ->
        (* Attempt merge on rigid variables *)
        let rigid_var =
          Hash_set.inter (rigid_vars t1) (rigid_vars t2)
          |> Hash_set.find ~f:(fun _ -> true)
        in
        (match rigid_var with
        | None -> raise Cannot_merge
        | Some rigid_var ->
          (* Determine the merged equational metadata *)
          let scope1 = scope t1 rigid_var in
          let scope2 = scope t2 rigid_var in
          Equations.Scope.max scope1 scope2, merge ())
      | Some ((former1, scope1), (former2, scope2)) ->
        (* Determine whether a clash would occur *)
        if Former.id former1 <> Former.id former2 then raise Clash;
        Former.iter2_exn former1 former2 ~f;
        Equations.Scope.max scope1 scope2, merge ()


    let get_min_expansive ~ctx t =
      (* TODO: Come up w/ clever datastructure to compute this efficiently *)
      Hashtbl.fold
        t.elts
        ~init:None
        ~f:(fun
             ~key:rigid_var
             ~data:{ is_expansive; scope = rigid_var_scope }
             acc
           ->
          if not is_expansive
          then acc
          else (
            match acc, Equations.Ctx.get_equation ctx.value rigid_var with
            | None, Some (rigid_type_scope, rigid_type) ->
              Some (rigid_var_scope, rigid_var, rigid_type_scope, rigid_type)
            | ( Some (_, _, rigid_type_scope', _)
              , Some (rigid_type_scope, rigid_type) )
              when rigid_type_scope < rigid_type_scope' ->
              Some (rigid_var_scope, rigid_var, rigid_type_scope, rigid_type)
            | _ -> acc))


    let expand ~ctx t rigid_var_scope rigid_var rigid_type_scope rigid_type =
      (* Add [rigid_type] to [t] *)
      (match Rigid_type.get_structure rigid_type with
      | Rigid_type.Var rigid_var' ->
        (* Add [rigid_var'] to [elts] w/ scope [scope] (if not already present) *)
        (match
           Hashtbl.add
             t.elts
             ~key:rigid_var'
             ~data:{ is_expansive = true; scope = rigid_type_scope }
         with
        | `Ok | `Duplicate -> ())
      | Rigid_type.Former former ->
        (* If we already have a former, don't expand *)
        (match t.former with
        | Some _ -> ()
        | None ->
          (* Convert [former] using [make] *)
          let former =
            Former.map
              ~f:
                (Rigid_type.to_type
                   ~make_var:ctx.make_var
                   ~make_former:ctx.make_former)
              former
          in
          t.former <- Some (former, rigid_type_scope)));
      (* Set [rigid_var] to be non-expansive *)
      Hashtbl.set
        t.elts
        ~key:rigid_var
        ~data:{ is_expansive = false; scope = rigid_var_scope }


    let expand1 ~ctx t =
      match get_min_expansive ~ctx t with
      | None -> raise Cannot_expand
      | Some (rigid_var_scope, rigid_var, rigid_type_scope, rigid_type) ->
        expand ~ctx t rigid_var_scope rigid_var rigid_type_scope rigid_type


    let expand2 ~ctx t1 t2 =
      (* Determine which view and which rigid variable we will be expanding *)
      let t, (rigid_var_scope, rigid_var, rigid_type_scope, rigid_type) =
        match get_min_expansive ~ctx t1, get_min_expansive ~ctx t2 with
        | None, None -> raise Cannot_expand
        | Some x, None -> t1, x
        | None, Some x -> t2, x
        | Some ((_, _, scope1, _) as x1), Some ((_, _, scope2, _) as x2) ->
          if scope1 <= scope2 then t1, x1 else t2, x2
      in
      expand ~ctx t rigid_var_scope rigid_var rigid_type_scope rigid_type
  end

  exception Clash

  (* [unify_exn] unifies two graphical types. No exception handling is 
     performed here. This is an internal function.
     
     Possible exceptions include:
     - [Former.Iter2], raised when executing Former.iter2 in {unify_form}.
     - [Clash], raised when incorrectly unifying a rigid variable.

     See {!unify}. 
  *)
  let rec unify_exn ~ctx t1 t2 = Union_find.union ~f:(unify_desc ~ctx) t1 t2

  (* [unify_desc desc1 desc2] unifies the descriptors of the graph types
     (of multi-equations). *)
  and unify_desc ~ctx desc1 desc2 =
    let scope, structure =
      unify_structure ~ctx desc1.structure desc2.structure
    in
    { id = desc1.id
    ; structure
    ; metadata = Metadata.merge desc1.metadata desc2.metadata
    ; scope =
        Equations.Scope.max desc1.scope (Equations.Scope.max desc2.scope scope)
    }


  (* [unify_structure structure1 structure2] unifies two graph type node
     structures. We handle rigid variables here. *)
  and unify_structure ~ctx structure1 structure2 =
    match structure1, structure2 with
    (* Unification of variables
    
       Unification is permitted between distinct variables only if 
       both variables are *not* rigid.
  
       In the case of 2 rigid variable, we raise [Cannot_unify_rigid_variable].
       We may unify a rigid variable with itself. However, this case does 
       not arise here since [Union_find.union] checks physical equality 
       before before [unify_structure] is executed. 
    *)
    | Rigid_var rigid_view1, Rigid_var rigid_view2 ->
      let scope, rigid_view = unify_rigid_view ~ctx rigid_view1 rigid_view2 in
      scope, Rigid_var rigid_view
    | Rigid_var rigid_view, Flexible_var | Flexible_var, Rigid_var rigid_view ->
      Equations.Scope.outermost_scope, Rigid_var rigid_view
    | Flexible_var, Flexible_var ->
      Equations.Scope.outermost_scope, Flexible_var
    (* Unification of variables (leaves) and type formers (internal nodes)
    
       We may unify a flexible variable with a type former, yielding
       the same type former. 
       Note that no propagation of metadata is performed. This is required
       by external modules. See {!generalization.ml}. 
    *)
    | Flexible_var, Former former | Former former, Flexible_var ->
      Equations.Scope.outermost_scope, Former former
    (* Unification between a rigid variable and a type former is not 
       permitted. We raise [Cannot_unify_rigid_variable]. *)
    | Rigid_var rigid_view, Former former | Former former, Rigid_var rigid_view
      ->
      let scope, rigid_view =
        unify_rigid_view_and_former ~ctx rigid_view former
      in
      scope, Rigid_var rigid_view
    (* Unification between type formers 
    
       We may unify type formers recursively. See {!unify_former}. 
    *)
    | Former former1, Former former2 ->
      ( Equations.Scope.outermost_scope
      , Former (unify_former ~ctx former1 former2) )


  (* [unify_former former1 former2] recursively unifies 2 type formers.

     Here we use our internal unification function [unify_exn],
     to allow exception propagation to the top-level call. *)

  and unify_former ~ctx former1 former2 =
    Former.iter2_exn former1 former2 ~f:(unify_exn ~ctx);
    former1


  and unify_rigid_view ~ctx rigid_view1 rigid_view2 =
    let rec loop () =
      try Rigid_view_.merge rigid_view1 rigid_view2 ~f:(unify_exn ~ctx) with
      | Rigid_view_.Clash -> raise Clash
      | Rigid_view_.Cannot_merge ->
        (try Rigid_view_.expand2 ~ctx rigid_view1 rigid_view2 with
        | Rigid_view_.Cannot_expand -> raise Clash);
        loop ()
    in
    loop ()


  and unify_rigid_view_and_former ~ctx rigid_view former =
    let rec loop () =
      match Rigid_view_.former rigid_view with
      | None ->
        (try Rigid_view_.expand1 ~ctx rigid_view with
        | Rigid_view_.Cannot_expand -> raise Clash);
        loop ()
      | Some (former', scope) ->
        (* No need to update [rigid_view.former], since we unify on the formers, ensuring they are equal *)
        Former.iter2_exn former former' ~f:(unify_exn ~ctx);
        (* Return scope of equation used. *)
        scope
    in
    let scope = loop () in
    scope, rigid_view


  exception Unify of Type.t * Type.t

  let unify ~ctx t1 t2 =
    try unify_exn ~ctx t1 t2 with
    | Former.Iter2 | Clash -> raise (Unify (t1, t2))


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
        | Former former ->
          (* Mark this node as grey. *)
          Hashtbl.set table ~key:t ~data:false;
          (* Visit children *)
          Former.iter ~f:loop former;
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
          | Rigid_var rigid_view -> rigid_var (Rigid_view.repr rigid_view) type_
          | Former former' -> former (Former.map ~f:loop former')
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
    let rec loop type_ =
      match get_structure type_ with
      | Flexible_var ->
        Hashtbl.set table ~key:type_ ~data:true;
        flexible_var type_
      | Rigid_var rigid_view ->
        Hashtbl.set table ~key:type_ ~data:true;
        rigid_var (Rigid_view.repr rigid_view) type_
      | Former former' ->
        if Hashtbl.mem table type_
        then (
          (* Mark this node as black *)
          Hashtbl.set table ~key:type_ ~data:true;
          flexible_var type_)
        else (
          (* Mark this node as grey. *)
          Hashtbl.set table ~key:type_ ~data:false;
          (* Visit children *)
          let result = former (Former.map ~f:loop former') in
          let status = Hashtbl.find_exn table type_ in
          Hashtbl.remove table type_;
          if status then mu type_ result else result)
    in
    loop type_
end
