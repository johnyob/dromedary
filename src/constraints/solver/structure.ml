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
  include Former

  type 'a ctx = unit

  exception Cannot_merge

  let merge ~ctx:() ~equate t1 t2 =
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


  let merge ~ctx ~equate t1 t2 =
    match t1, t2 with
    | Var, t | t, Var -> t
    | Structure structure1, Structure structure2 ->
      Structure (Structure.merge ~ctx ~equate structure1 structure2)
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

  let merge ~ctx ~equate t1 t2 =
    let ( === ) t1 t2 = Id.id t1 = Id.id t2 in
    let ( =~ ) t1 t2 = Structure.merge ~ctx:ctx.super_ ~equate t1 t2 in
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
      match Abbrev.Ctx.find ctx.abbrev_ctx t1 with
      | None ->
        (match Abbrev.Ctx.find ctx.abbrev_ctx t2 with
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

    module Rigid_Structure = struct
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

      exception Cannot_merge = Structure.Cannot_merge

      let merge ~ctx ~equate t1 t2 =
        let ( =~- ) type_ structure =
          let type_' = ctx.make structure in
          equate type_ type_'
        in
        let add_equation rigid_var structure =
          Log.debug (fun m -> m "Adding equation for %d" rigid_var);
          let type_ = ctx.make structure in
          ctx.equations_ctx
            <- Equations.Ctx.add_equation
                 ctx.equations_ctx
                 rigid_var
                 type_
                 ctx.scope
        in
        match t1, t2 with
        | Structure structure1, Structure structure2 ->
          Structure
            (Structure.merge ~ctx:ctx.super_ ~equate structure1 structure2)
        | Rigid_var rigid_var1, Rigid_var rigid_var2
          when Rigid_var.compare rigid_var1 rigid_var2 = 0 ->
          Rigid_var rigid_var1
        | Rigid_var rigid_var, _ ->
          (match Equations.Ctx.get_equation ctx.equations_ctx rigid_var with
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
          (match Equations.Ctx.get_equation ctx.equations_ctx rigid_var with
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

    module Structure = First_order (Rigid_Structure)
    module Unifier = Unifier.Make (Structure)

    type t = Unifier.Type.t [@@deriving sexp_of]

    let make = Unifier.Type.make
    let make_var () = make Var
    let make_rigid_var rigid_var = make (Structure (Rigid_var rigid_var))
    let make_structure structure = make (Structure (Structure structure))

    let copy t =
      let copied : (t, t) Hashtbl.t = Hashtbl.create (module Unifier.Type) in
      let rec copy t =
        try Hashtbl.find_exn copied t with
        | Not_found_s _ ->
          let new_t =
            make (Unifier.Type.structure t |> Structure.map ~f:copy)
          in
          Hashtbl.set copied ~key:t ~data:new_t;
          new_t
      in
      copy t


    let structure = Unifier.Type.structure
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
        (try Rigid_type.Unifier.unify ~ctx type1 type2 with 
          _ -> raise Inconsistent);
        ctx.equations_ctx


      let get_equation t rigid_var = Map.find t rigid_var
    end
  end

  type 'a t =
    { mutable scope : Equations.Scope.t
    ; repr : 'a repr
    }
  [@@deriving sexp_of]

  and 'a repr =
    | Rigid_var of Rigid_var.t
    | Structure of 'a Structure.t

  let repr t = t.repr
  let make repr = { scope = Equations.Scope.outermost_scope; repr }
  let scope t = t.scope
  let update_scope t scope = if t.scope < scope then t.scope <- scope

  let iter t ~f =
    match repr t with
    | Rigid_var _ -> ()
    | Structure structure -> Structure.iter structure ~f


  let fold t ~f ~init =
    match repr t with
    | Rigid_var _ -> init
    | Structure structure -> Structure.fold structure ~f ~init


  let map t ~f =
    { t with
      repr =
        (match repr t with
        | Rigid_var rigid_var -> Rigid_var rigid_var
        | Structure structure -> Structure (Structure.map structure ~f))
    }


  type 'a ctx =
    { equations_ctx : Equations.Ctx.t
    ; make : 'a t -> 'a
    ; super_ : 'a Structure.ctx
    }

  let convert_rigid_type ~ctx rigid_type =
    let rec loop rigid_type =
      (match Rigid_type.structure rigid_type with
      | Var -> assert false
      | Structure (Rigid_var rigid_var) -> Rigid_var rigid_var
      | Structure (Structure structure) ->
        let structure = Structure.map structure ~f:loop in
        Structure structure)
      |> make
      |> ctx.make
    in
    loop rigid_type


  exception Cannot_merge = Structure.Cannot_merge

  let merge ~ctx ~equate t1 t2 =
    (* [type_ =~- structure] "unifies" the structure [structure] with type [type_] *)
    let ( =~- ) type_ structure =
      let type_' = ctx.make structure in
      equate type_ type_'
    in
    (* The new scope is the maximum of the 2 scopes. 

       We use a reference here, as [scope] may be updated when
       computing the representation. *)
    let scope = ref (Equations.Scope.max t1.scope t2.scope) in
    (* We perform case analysis on the representation. 
       Where rigid variables are concerned, we expand only when necessary. 

       Optimization: Expansions could be memoized, as in Morel. 
    *)
    let repr =
      match repr t1, repr t2 with
      | Structure structure1, Structure structure2 ->
        Structure
          (Structure.merge ~ctx:ctx.super_ ~equate structure1 structure2)
      | Rigid_var rigid_var1, Rigid_var rigid_var2
        when Rigid_var.compare rigid_var1 rigid_var2 = 0 -> Rigid_var rigid_var1
      | Rigid_var rigid_var1, Rigid_var rigid_var2 ->
        let rigid_var, rigid_type, scope', t =
          match Equations.Ctx.get_equation ctx.equations_ctx rigid_var1 with
          | Some (rigid_type, scope') -> 
            Log.debug (fun m -> m "Using equation for %d with scope %d" rigid_var1 scope');
            rigid_var1, rigid_type, scope', t2
          | None ->
            (match Equations.Ctx.get_equation ctx.equations_ctx rigid_var2 with
            | Some (rigid_type, scope') -> 
              Log.debug (fun m -> m "Using equation for %d with scope %d" rigid_var2 scope');
              rigid_var2, rigid_type, scope', t1
            | None -> raise Cannot_merge)
        in
        (* Convert [rigid_type] to ['a] type. *)
        let t' = convert_rigid_type ~ctx rigid_type in
        (* Merge [t2'] and [t1]. *)
        t' =~- t;
        (* Update scope *)
        Log.debug (fun m -> m "Updating scope: %d = %d w/ scopes %d %d" rigid_var1 rigid_var2 !scope scope');
        if !scope < scope' then scope := scope';
        (* Representative is the rigid variable *)
        Rigid_var rigid_var
      | Rigid_var rigid_var, _ ->
        (match Equations.Ctx.get_equation ctx.equations_ctx rigid_var with
        | None -> raise Cannot_merge
        | Some (rigid_type, scope') ->
          Log.debug (fun m -> m "Using equation for %d" rigid_var);
          (* Convert [rigid_type] to ['a] type. *)
          let t1' = convert_rigid_type ~ctx rigid_type in
          (* Merge [t2'] and [t1]. *)
          t1' =~- t2;
          (* Update scope *)
          if !scope < scope' then scope := scope';
          (* Representative is the rigid variable *)
          Rigid_var rigid_var)
      | _, Rigid_var rigid_var ->
        (match Equations.Ctx.get_equation ctx.equations_ctx rigid_var with
        | None -> raise Cannot_merge
        | Some (rigid_type, scope') ->
          Log.debug (fun m -> m "Using equation for %d" rigid_var);
          (* Convert [rigid_type] to ['a] type. *)
          let t2' = convert_rigid_type ~ctx rigid_type in
          (* Merge [t2'] and [t1]. *)
          t2' =~- t1;
          (* Update scope *)
          if !scope < scope' then scope := scope';
          (* Representative is the rigid variable *)
          Rigid_var rigid_var)
    in
    { scope = !scope; repr }
end

module Rows (Label : Comparable.S) (Structure : S) = struct
  module Label = struct
    include Label

    (* Add [sexp_of_t] for label into module scope for 
       below [@@deriving sexp_of] *)
    let sexp_of_t = comparator.sexp_of_t
  end

  type 'a t =
    | Structure of 'a Structure.t
    | Row_cons of Label.t * 'a * 'a
    | Row_uniform of 'a
  [@@deriving sexp_of]

  type 'a ctx =
    { make_var : unit -> 'a
    ; make_structure : 'a t -> 'a
    ; super_ : 'a Structure.ctx
    }

  let map t ~f =
    match t with
    | Structure structure -> Structure (Structure.map structure ~f)
    | Row_cons (label, t1, t2) -> Row_cons (label, f t1, f t2)
    | Row_uniform t -> Row_uniform (f t)


  let iter t ~f =
    match t with
    | Structure structure -> Structure.iter structure ~f
    | Row_cons (_, t1, t2) ->
      f t1;
      f t2
    | Row_uniform t -> f t


  let fold t ~f ~init =
    match t with
    | Structure structure -> Structure.fold structure ~f ~init
    | Row_cons (_, t1, t2) -> f t2 (f t1 init)
    | Row_uniform t -> f t init


  exception Cannot_merge = Structure.Cannot_merge

  let merge ~ctx ~equate t1 t2 =
    let ( =~ ) = equate in
    let ( =~- ) a structure = a =~ ctx.make_structure structure in

    let is_row_cons l t = 
      let t1, t2 = ctx.make_var (), ctx.make_var () in
      t =~- Row_cons (l, t1, t2);
      t1, t2
    in

    let is_row_uniform t = 
      let t' = ctx.make_var () in
      t =~- Row_uniform t';
      t'
    in

    match t1, t2 with
    | Structure structure1, Structure structure2 ->
      Structure (Structure.merge ~ctx:ctx.super_ ~equate structure1 structure2)
    | Row_uniform t1, Row_uniform t2 ->
      t1 =~ t2;
      Row_uniform t1
    | Row_cons (label1, t11, t12), Row_cons (label2, t21, t22)
      when Label.compare label1 label2 = 0 ->
      (* The labels [label1] and [label2] are equal. *)
      t11 =~ t21;
      t12 =~ t22;
      (* We arbitrary return a Row_cons. *)
      t1
    | Row_cons (label1, t11, t12), Row_cons (label2, t21, t22) ->
      (* The labels [label1] and [label2] are not equal. *)
      let t = ctx.make_var () in
      (* Unify the label of t1 with a Row containing (label2) *)
      t12 =~- Row_cons (label2, t21, t);
      t22 =~- Row_cons (label1, t11, t);
      (* We arbitrary return a Row_cons. We wish to maintain some sorted
         order to the Rows, as this gives us canoncial rows. *)
      if Label.compare label1 label2 < 0 then t1 else t2
    | Row_cons (_, t11, t12), (Row_uniform t as t2)
    | (Row_uniform t as t2), Row_cons (_, t11, t12) ->
      t11 =~ t;
      t12 =~- t2;
      t2
    | (Row_cons (l1, t11, t12) as t1), Structure t2
    | Structure t2, (Row_cons (l1, t11, t12) as t1) ->
      (* TODO: Understand WHY the distributive property for formers (structures) is required. *)
      (* The children of [t2] must be of the form: [(l1: _; _)] (according to EMLTI). *)
      let t11', t12' = 
        let t11_12 = Structure.map t2 ~f:(is_row_cons l1) in
        Structure.map ~f:fst t11_12, Structure.map ~f:snd t11_12
      in
      t11 =~- Structure t11';
      t12 =~- Structure t12';
      t1
    | (Row_uniform t as t1), Structure t2
    | Structure t2, (Row_uniform t as t1) ->
      let t' = Structure.map t2 ~f:is_row_uniform in
      t =~- Structure t';
      t1
end