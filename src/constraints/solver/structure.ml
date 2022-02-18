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

  type 'a ctx = unit

  exception Cannot_merge

  let merge ~ctx:() ~equate (t1, ()) (t2, ()) =
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


  let merge ~ctx ~equate (desc1, metadata1) (desc2, metadata2) =
    match desc1, desc2 with
    | Var, desc | desc, Var -> desc
    | Structure desc1, Structure desc2 ->
      Structure
        (Structure.merge ~ctx ~equate (desc1, metadata1) (desc2, metadata2))
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

  type 'a ctx =
    { abbrev_ctx : Abbrev.Ctx.t
    ; make_structure : 'a Structure.t -> 'a
    ; make_var : unit -> 'a
    ; super_ : 'a Structure.ctx
    }

  let actx t = t.abbrev_ctx
  let sctx t = t.super_
  let make t = t

  let convert_abbrev ~ctx abbrev =
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
          | Var -> ctx.make_var ()
          | Structure structure ->
            ctx.make_structure (Structure.map ~f:copy structure)
        in
        Hashtbl.set copied ~key:type_ ~data:new_type;
        new_type
    in
    let abbrev_structure = Structure.map ~f:copy abbrev_structure in
    let abbrev_type = copy abbrev_type in
    abbrev_structure, abbrev_type


  let repr t = t

  let merge ~(ctx : _ ctx) ~equate (t1, metadata1) (t2, metadata2) =
    let ( === ) t1 t2 = Id.id t1 = Id.id t2 in
    let ( =~ ) t1 t2 =
      Structure.merge
        ~ctx:(sctx ctx)
        ~equate
        (t1, Metadata.super_ metadata1)
        (t2, Metadata.super_ metadata2)
    in
    let ( =~- ) a t =
      let a' = ctx.make_structure t in
      equate a a'
    in
    let expand_with_abbrev t ~abbrev =
      (* Expand the abbreviation of [t] *)
      let abbrev_structure, abbrev_type = convert_abbrev ~ctx abbrev in
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


  let merge ~ctx ~equate (desc1, metadata1) (desc2, metadata2) =
    match desc1, desc2 with
    | Rigid_var rigid_var1, Rigid_var rigid_var2
      when Rigid_var.compare rigid_var1 rigid_var2 = 0 -> Rigid_var rigid_var1
    | Structure desc1, Structure desc2 ->
      Structure
        (Structure.merge ~ctx ~equate (desc1, metadata1) (desc2, metadata2))
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

module Abbreviations
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


      let make_var () = make Var
      let make_structure structure = make (Structure structure)
      let structure t = !t.structure
      let id t = !t.id
      let compare t1 t2 = Int.compare (id t1) (id t2)
      let hash = id
    end

    type t =
      { id : int
      ; abbrev : Type.t Structure.t * Type.t
      }

    let make abbrev_structure abbrev_type =
      let id = Id.id abbrev_structure in
      Structure.iter abbrev_structure ~f:(fun t ->
          match Type.structure t with
          | Var -> ()
          | _ -> assert false);
      { id; abbrev = abbrev_structure, abbrev_type }


    let id t = t.id
    let abbrev t = t.abbrev

    module Ctx = struct
      type nonrec t = (Int.t, t, Int.comparator_witness) Map.t

      let empty : t = Map.empty (module Int)
      let add (t : t) ~abbrev = Map.set t ~key:(id abbrev) ~data:abbrev
      let find (t : t) structure = Map.find t (Id.id structure)
    end
  end

  include Structure

  type 'a ctx =
    { abbrev_ctx : Abbrev.Ctx.t
    ; make_structure : 'a Structure.t -> 'a
    ; make_var : unit -> 'a
    ; super_ : 'a Structure.ctx
    }

  let actx t = t.abbrev_ctx
  let sctx t = t.super_
  let make t = t

  let convert_abbrev ~ctx abbrev =
    let abbrev_structure, abbrev_type = Abbrev.abbrev abbrev in
    let copied : (Abbrev.Type.t, _) Hashtbl.t =
      Hashtbl.create (module Abbrev.Type)
    in
    (* Assume [abbrev_type] is acyclic *)
    let rec copy type_ =
      try Hashtbl.find_exn copied type_ with
      | Not_found_s _ ->
        let new_type =
          match Abbrev.Type.structure type_ with
          | Var -> ctx.make_var ()
          | Structure structure ->
            ctx.make_structure (Structure.map ~f:copy structure)
        in
        Hashtbl.set copied ~key:type_ ~data:new_type;
        new_type
    in
    let abbrev_structure = Structure.map ~f:copy abbrev_structure in
    let abbrev_type = copy abbrev_type in
    abbrev_structure, abbrev_type


  let repr t = t

  let merge ~ctx ~equate (t1, metadata1) (t2, metadata2) =
    let ( === ) t1 t2 = Id.id t1 = Id.id t2 in
    let ( =~ ) t1 t2 =
      Structure.merge ~ctx:(sctx ctx) ~equate (t1, metadata1) (t2, metadata2)
    in
    let ( =~- ) a t =
      let a' = ctx.make_structure t in
      equate a a'
    in
    let expand_with_abbrev t ~abbrev =
      (* Expand the abbreviation of [t] *)
      let abbrev_structure, abbrev_type = convert_abbrev ~ctx abbrev in
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
          t1)
      | Some abbrev ->
        (* Expand [t2] to [t2'], and merge [t2'] and [t1]. *)
        let t1' = expand_with_abbrev t1 ~abbrev in
        (* Merge [t2'] and [t1]. *)
        t1' =~- t2;
        t2)
end

module Ambivalent (Structure : S) = struct
  module Rigid_type = struct
    module Equations = struct
      module Scope = struct
        type t = int [@@deriving sexp_of]

        let max = max
        let outermost_scope = 0
      end

      type 'a scoped = 'a * Scope.t

      module Ctx = struct
        type 'a t = (Rigid_var.t, 'a scoped, Rigid_var.comparator_witness) Map.t

        let get_equation (t : _ t) rigid_var = Map.find t rigid_var

        let add_equation (t : _ t) rigid_var structure scope =
          Map.set t ~key:rigid_var ~data:(structure, scope)
      end
    end

    module Structure__ = struct
      module Metadata = Structure.Metadata

      type 'a t =
        | Rigid_var of Rigid_var.t
        | Structure of 'a Structure.t
      [@@deriving sexp_of]

      let iter t ~f =
        match t with
        | Rigid_var _ -> ()
        | Structure structure -> Structure.iter structure ~f


      let fold t ~f ~init =
        match t with
        | Rigid_var _ -> init
        | Structure structure -> Structure.fold structure ~f ~init


      let map t ~f =
        match t with
        | Rigid_var rigid_var -> Rigid_var rigid_var
        | Structure structure -> Structure (Structure.map structure ~f)


      type 'a ctx =
        { mutable equations_ctx : 'a Equations.Ctx.t
        ; mutable scope : Equations.Scope.t
        ; copy : 'a -> 'a
        ; make : 'a t -> 'a
        ; super_ : 'a Structure.ctx
        }

      let ectx t = t.equations_ctx
      let sctx t = t.super_

      exception Cannot_merge = Structure.Cannot_merge

      let merge ~ctx ~equate (t1, metadata1) (t2, metadata2) =
        let ( =~ ) = equate in
        let ( =~- ) type_ structure =
          let type_' = ctx.make structure in
          type_ =~ type_'
        in
        let add_equation rigid_var structure =
          let type_ = ctx.make structure in
          ctx.equations_ctx
            <- Equations.Ctx.add_equation (ectx ctx) rigid_var type_ ctx.scope
        in
        match t1, t2 with
        | Structure structure1, Structure structure2 ->
          Structure
            (Structure.merge
               ~ctx:(sctx ctx)
               ~equate
               (structure1, metadata1)
               (structure2, metadata2))
        | Rigid_var rigid_var1, Rigid_var rigid_var2
          when Rigid_var.compare rigid_var1 rigid_var2 = 0 ->
          Rigid_var rigid_var1
        | Rigid_var rigid_var, _ ->
          (match Equations.Ctx.get_equation (ectx ctx) rigid_var with
          | None -> add_equation rigid_var t2
          | Some (rigid_type, scope) ->
            (* Convert [rigid_type] to ['a] type. *)
            let t1' = ctx.copy rigid_type in
            (* Update scope *)
            if ctx.scope < scope then ctx.scope <- scope;
            (* Merge [t2'] and [t1]. *)
            t1' =~- t2);
          t1
        | _, Rigid_var rigid_var ->
          (match Equations.Ctx.get_equation (ectx ctx) rigid_var with
          | None -> add_equation rigid_var t1
          | Some (rigid_type, scope) ->
            (* Convert [rigid_type] to ['a] type. *)
            let t2' = ctx.copy rigid_type in
            (* Update scope *)
            if ctx.scope < scope then ctx.scope <- scope;
            (* Merge [t2'] and [t1]. *)
            t2' =~- t1);
          t2
    end

    module Structure = First_order (Structure__)
    module Unifier = Unifier.Make (Structure)

    type t = Unifier.Type.t [@@deriving sexp_of]

    let make structure =
      Unifier.Type.make structure (Structure.Metadata.empty ())


    let make_var () = make Var
    let make_rigid_var rigid_var = make (Structure (Rigid_var rigid_var))
    let make_structure structure = make (Structure (Structure structure))

    let copy t =
      let copied : (t, t) Hashtbl.t = Hashtbl.create (module Unifier.Type) in
      let rec copy t =
        try Hashtbl.find_exn copied t with
        | Not_found_s _ ->
          let new_t =
            make (Unifier.Type.get_structure t |> Structure.map ~f:copy)
          in
          Hashtbl.set copied ~key:t ~data:new_t;
          new_t
      in
      copy t
  end

  module Equations = struct
    include Rigid_type.Equations

    module Ctx = struct
      type t = Rigid_type.t Ctx.t

      let empty = Map.empty (module Rigid_var)

      exception Inconsistent = Rigid_type.Structure.Cannot_merge

      let add ~ctx t type1 type2 scope =
        let ctx : Rigid_type.t Rigid_type.Structure.ctx =
          { equations_ctx = t
          ; scope
          ; make = (fun structure -> Rigid_type.make (Structure structure))
          ; copy = Rigid_type.copy
          ; super_ = ctx
          }
        in
        Rigid_type.Unifier.unify ~ctx type1 type2;
        ctx.equations_ctx


      let get_equation t rigid_var = Map.find t rigid_var
    end
  end

  module Metadata = struct
    type 'a t =
      { mutable scope : Equations.Scope.t
      ; super_ : 'a Structure.Metadata.t
      }
    [@@deriving sexp_of]

    let empty () =
      { scope = Equations.Scope.outermost_scope
      ; super_ = Structure.Metadata.empty ()
      }


    let merge t1 t2 =
      { scope = Equations.Scope.max t1.scope t2.scope
      ; super_ = Structure.Metadata.merge t1.super_ t2.super_
      }


    let scope t = t.scope
    let update_scope t scope = if t.scope < scope then t.scope <- scope
    let super_ t = t.super_
  end

  type 'a t =
    | Rigid_var of Rigid_var.t
    | Structure of 'a Structure.t
  [@@deriving sexp_of]

  let iter t ~f =
    match t with
    | Rigid_var _ -> ()
    | Structure structure -> Structure.iter structure ~f


  let fold t ~f ~init =
    match t with
    | Rigid_var _ -> init
    | Structure structure -> Structure.fold structure ~f ~init


  let map t ~f =
    match t with
    | Rigid_var rigid_var -> Rigid_var rigid_var
    | Structure structure -> Structure (Structure.map structure ~f)


  type 'a ctx =
    { equations_ctx : Equations.Ctx.t
    ; make : 'a t -> 'a
    ; super_ : 'a Structure.ctx
    }

  let ectx t = t.equations_ctx
  let sctx t = t.super_

  let convert_rigid_type ~ctx rigid_type =
    let rec loop rigid_type =
      let module Unifier = Rigid_type.Unifier in
      ctx.make
        (match Unifier.Type.get_structure rigid_type with
        | Var -> assert false
        | Structure (Rigid_var rigid_var) -> Rigid_var rigid_var
        | Structure (Structure structure) ->
          let structure = Structure.map structure ~f:loop in
          Structure structure)
    in
    loop rigid_type


  exception Cannot_merge = Structure.Cannot_merge

  let merge ~ctx ~equate (t1, metadata1) (t2, metadata2) =
    let ( =~- ) type_ structure =
      let type_' = ctx.make structure in
      equate type_ type_'
    in
    match t1, t2 with
    | Structure structure1, Structure structure2 ->
      Structure
        (Structure.merge
           ~ctx:(sctx ctx)
           ~equate
           (structure1, Metadata.super_ metadata1)
           (structure2, Metadata.super_ metadata2))
    | Rigid_var rigid_var1, Rigid_var rigid_var2
      when Rigid_var.compare rigid_var1 rigid_var2 = 0 -> Rigid_var rigid_var1
    | Rigid_var rigid_var, _ ->
      (match Equations.Ctx.get_equation (ectx ctx) rigid_var with
      | None -> raise Cannot_merge
      | Some (rigid_type, scope) ->
        (* Convert [rigid_type] to ['a] type. *)
        let t1' = convert_rigid_type ~ctx rigid_type in
        (* Merge [t2'] and [t1]. *)
        t1' =~- t2;
        (* Update scope *)
        Metadata.update_scope metadata1 scope;
        t1)
    | _, Rigid_var rigid_var ->
      (match Equations.Ctx.get_equation (ectx ctx) rigid_var with
      | None -> raise Cannot_merge
      | Some (rigid_type, scope) ->
        (* Convert [rigid_type] to ['a] type. *)
        let t2' = convert_rigid_type ~ctx rigid_type in
        (* Merge [t2'] and [t1]. *)
        t2' =~- t1;
        (* Update scope *)
        Metadata.update_scope metadata2 scope;
        t2)
end