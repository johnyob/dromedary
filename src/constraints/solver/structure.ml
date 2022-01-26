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

  type ctx = unit
  type 'a expansive = unit

  exception Cannot_merge

  let merge ~expansive:() ~ctx:() ~equate t1 t2 =
    (try Former.iter2_exn t1 t2 ~f:equate with
    | Former.Iter2 -> raise Cannot_merge);
    t1
end

module First_order (Structure : S) = struct
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


  type 'a expansive = 'a Structure.expansive
  type ctx = Structure.ctx

  exception Cannot_merge

  let merge ~expansive ~ctx ~equate t1 t2 =
    match t1, t2 with
    | Var, structure | structure, Var -> structure
    | Structure structure1, Structure structure2 ->
      (try
         Structure
           (Structure.merge ~expansive ~ctx ~equate structure1 structure2)
       with
      | Structure.Cannot_merge -> raise Cannot_merge)
end

module Abbreviations
    (Structure : S)
    (Id : Identifiable with type 'a t := 'a Structure.t) =
struct
  module Abbrev_type = struct
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

  module Abbrev = struct
    type t =
      { id : int
      ; abbrev : Abbrev_type.t Structure.t * Abbrev_type.t
      }

    let make abbrev_structure abbrev_type =
      let id = Id.id abbrev_structure in
      { id; abbrev = abbrev_structure, abbrev_type }


    let id t = t.id
    let abbrev t = t.abbrev
  end

  module Ctx = struct
    type t = (Int.t, Abbrev.t, Int.comparator_witness) Map.t

    let empty : t = Map.empty (module Int)
    let add (t : t) ~abbrev = Map.set t ~key:(Abbrev.id abbrev) ~data:abbrev
    let has_abbrev (t : t) id = Map.mem t id

    exception Not_found

    let find_abbrev (t : t) id =
      match Map.find t id with
      | Some abbrev -> abbrev
      | None -> raise Not_found
  end

  include Structure

  let actx = fst
  let sctx = snd
  let make t = t

  type 'a expansive =
    { make_structure : 'a Structure.t -> 'a
    ; make_var : unit -> 'a
    ; sexpansive : 'a Structure.expansive
    }

  let convert_abbrev ~expansive abbrev =
    let abbrev_structure, abbrev_type = Abbrev.abbrev abbrev in
    let copied : (Abbrev_type.t, _) Hashtbl.t =
      Hashtbl.create (module Abbrev_type)
    in
    (* Assume [abbrev_type] is acyclic *)
    let rec copy type_ =
      try Hashtbl.find_exn copied type_ with
      | Not_found_s _ ->
        let new_type =
          match Abbrev_type.structure type_ with
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

  let merge ~expansive ~ctx ~equate t1 t2 =
    let ( =- ) =
      Structure.merge ~expansive:expansive.sexpansive ~ctx:(sctx ctx) ~equate
    in
    let ( =~ ) a t =
      let a' = expansive.make_structure t in
      equate a a'
    in
    let expand t =
      (* Determine abbreviation of [t] *)
      let abbrev = Ctx.find_abbrev (actx ctx) (Id.id t) in
      (* Expand the abbreviation of [t] *)
      let abbrev_structure, abbrev_type = convert_abbrev ~expansive abbrev in
      (* Equate the variables and children of [t]. *)
      ignore (t =- abbrev_structure : _ Structure.t);
      abbrev_type
    in
    (* TODO: Perhaps remove [has_abbrev] and use match on options instead. *)
    if Id.id t1 = Id.id t2
    then t1 =- t2
    else if Ctx.has_abbrev (actx ctx) (Id.id t1)
    then (
      (* Expand [t1] to [t1'], and merge [t1'] and [t2] *)
      let t1' = expand t1 in
      (* Merge [t1'] and [t2]. *)
      t1' =~ t2;
      (* If the above merge is successful, then return [t1]. *)
      t1)
    else if Ctx.has_abbrev (actx ctx) (Id.id t2)
    then (
      let t2' = expand t2 in
      (* Merge [t1] and [t2']. *)
      t2' =~ t1;
      t2)
    else raise Cannot_merge
end

module Ambivalent (Structure : S) = struct
  module Rigid_type = struct
    type t =
      | Rigid_var of Rigid_var.t
      | Structure of t Structure.t
  end

  module Equations = struct
    module Scope = struct
      type t = int [@@deriving sexp_of]

      (* let min = min *)
      let max = max
      let outermost_scope = 0
    end

    type 'a scoped = 'a * Scope.t

    module Ctx = struct
      type t =
        (Rigid_var.t, Rigid_type.t scoped, Rigid_var.comparator_witness) Map.t

      let empty = Map.empty (module Rigid_var)

      exception Inconsistent

      let rec add_equation ~expansive ~ctx t rigid_var type1 scope =
        match Map.find !t rigid_var with
        | Some (type2, _) -> add_equations ~expansive ~ctx t type1 type2 scope
        | None -> t := Map.set !t ~key:rigid_var ~data:(type1, scope)


      and add_equations ~expansive ~ctx t type1 type2 scope =
        let open Rigid_type in
        match type1, type2 with
        | Rigid_var rigid_var, type2 ->
          add_equation ~expansive ~ctx t rigid_var type2 scope
        | type1, Rigid_var rigid_var ->
          add_equation ~expansive ~ctx t rigid_var type1 scope
        | Structure structure1, Structure structure2 ->
          ignore
            (Structure.merge
               ~expansive
               ~ctx
               ~equate:(fun type1' type2' ->
                 add_equations ~expansive ~ctx t type1' type2' scope)
               structure1
               structure2
              : _ Structure.t)


      let add ~expansive ~ctx t type1 type2 scope =
        try
          let t = ref t in
          add_equations ~expansive ~ctx t type1 type2 scope;
          !t
        with
        | Structure.Cannot_merge -> raise Inconsistent


      let get_equation t rigid_var = Map.find t rigid_var
    end
  end

  type 'a t =
    { mutable desc : 'a desc
    ; mutable scope : Equations.Scope.t
    }
  [@@deriving sexp_of]

  and 'a desc =
    | Flexible_var
    | Rigid_var of Rigid_var.t
    | Structure of 'a Structure.t

  let make desc = { desc; scope = Equations.Scope.outermost_scope }
  let desc t = t.desc
  let set_desc t desc' = t.desc <- desc'
  let scope t = t.scope
  let update_scope t scope = if t.scope < scope then t.scope <- scope

  let iter t ~f =
    match t.desc with
    | Flexible_var | Rigid_var _ -> ()
    | Structure structure -> Structure.iter structure ~f


  let fold t ~f ~init =
    match t.desc with
    | Flexible_var | Rigid_var _ -> init
    | Structure structure -> Structure.fold structure ~f ~init


  let map t ~f =
    let map_desc t ~f =
      match t with
      | Flexible_var -> Flexible_var
      | Rigid_var rigid_var -> Rigid_var rigid_var
      | Structure structure -> Structure (Structure.map structure ~f)
    in
    { t with desc = map_desc t.desc ~f }


  type ctx = Equations.Ctx.t * Structure.ctx

  type 'a expansive =
    { make : 'a t -> 'a
    ; sexpansive : 'a Structure.expansive
    }

  let ectx = fst
  let sctx = snd

  exception Cannot_expand

  let convert_rigid_type ~expansive rigid_type =
    let rec loop rigid_type =
      let open Rigid_type in
      expansive.make
        (match rigid_type with
        | Rigid_var rigid_var -> make (Rigid_var rigid_var)
        | Structure structure ->
          let structure = Structure.map structure ~f:loop in
          make (Structure structure))
    in
    loop rigid_type


  (* [expand ~expansive ~ctx rigid_var] returns a ['a Structure.t, scope] determined by [ctx].
     Otherwise, raises Cannot_expansive *)
  let expand ~expansive ~ctx rigid_var =
    let rec loop rigid_var scope =
      let open Rigid_type in
      match Equations.Ctx.get_equation (ectx ctx) rigid_var with
      | Some (Rigid_var rigid_var, scope') ->
        loop rigid_var (Equations.Scope.max scope scope')
      | Some (Structure structure, scope') ->
        (* Convert [structure] using [term]. *)
        let structure =
          Structure.map structure ~f:(convert_rigid_type ~expansive)
        in
        structure, Equations.Scope.max scope scope'
      | None -> raise Cannot_expand
    in
    loop rigid_var Equations.Scope.outermost_scope


  (* [is_equivalent] *)
  let is_equivalent ~ctx rigid_var1 rigid_var2 =
    let rec loop rigid_var1 rigid_var2 scope =
      let open Rigid_type in
      if rigid_var1 = rigid_var2
      then true, scope
      else (
        match Equations.Ctx.get_equation (ectx ctx) rigid_var1 with
        | Some (Rigid_var rigid_var2', scope') ->
          if rigid_var2 = rigid_var2'
          then true, max scope scope'
          else loop rigid_var2' rigid_var2 (Equations.Scope.max scope scope')
        | _ -> false, Equations.Scope.outermost_scope)
    in
    let first, scope1 =
      loop rigid_var1 rigid_var2 Equations.Scope.outermost_scope
    in
    if first
    then true, scope1
    else loop rigid_var2 rigid_var1 Equations.Scope.outermost_scope


  exception Cannot_merge = Structure.Cannot_merge

  let merge_desc ~expansive ~ctx ~equate t1 t2 =
    match t1, t2 with
    | Flexible_var, desc | desc, Flexible_var ->
      desc, Equations.Scope.outermost_scope
    | Structure structure1, Structure structure2 ->
      ( Structure
          (Structure.merge
             ~expansive:expansive.sexpansive
             ~ctx:(sctx ctx)
             ~equate
             structure1
             structure2)
      , Equations.Scope.outermost_scope )
    | Rigid_var rigid_var, Structure structure
    | Structure structure, Rigid_var rigid_var ->
      (* Expand rigid variable to structure under [ectx ctx]. *)
      let structure', scope =
        try expand ~expansive ~ctx rigid_var with
        | Cannot_expand -> raise Cannot_merge
      in
      (* Equate the 2 structures. *)
      ignore
        (Structure.merge
           ~expansive:expansive.sexpansive
           ~ctx:(sctx ctx)
           ~equate
           structure
           structure'
          : _ Structure.t);
      (* Descriptor remains as [Rigid_var] *)
      Rigid_var rigid_var, scope
    | Rigid_var rigid_var1, Rigid_var rigid_var2 ->
      (* Determine whether [rigid_var1], [rigid_var2] are equivalent under
         [ectx ctx]. *)
      let is_equiv, scope = is_equivalent ~ctx rigid_var1 rigid_var2 in
      if not is_equiv then raise Cannot_merge;
      (* Return arbitrary rigid variable *)
      Rigid_var rigid_var1, scope


  let merge ~expansive ~ctx ~equate t1 t2 =
    let desc, scope = merge_desc ~expansive ~equate ~ctx t1.desc t2.desc in
    { desc
    ; scope = Equations.Scope.max t1.scope (Equations.Scope.max t2.scope scope)
    }

  (* let merge_scoped scoped1 scoped2 ~f =
    let t1, scope1 = scoped1 in
    let t2, scope2 = scoped2 in
    f t1 t2, Equations.Scope.min scope1 scope2


  let decompose_scope (_, scope1) (_, scope2) =
    Equations.Scope.max scope1 scope2


  let merge_structure t1 t2 =
    match t1.structure, t2.structure with
    | None, structure | structure, None -> structure
    | Some structure1, Some structure2 ->
      (* We select an arbitrary structure, namely the first.*)
      Some
        (merge_scoped structure1 structure2 ~f:(fun structure _ -> structure))


  let merge_rigid_vars t1 t2 =
    Hashtbl.merge t1.rigid_vars t2.rigid_vars ~f:(fun ~key:_ -> function
      | `Left desc | `Right desc -> Some desc
      | `Both (desc1, desc2) ->
        Some
          (merge_scoped desc1 desc2 ~f:(fun is_expansive1 is_expansive2 ->
               is_expansive1 && is_expansive2)))


  let find_decomposable_rigid_var_scope t1 t2 =
    Hash_set.inter (rigid_vars t1) (rigid_vars t2)
    |> Hash_set.fold ~init:None ~f:(fun acc rigid_var ->
           let find_scope t = Hashtbl.find_exn t.rigid_vars rigid_var |> snd in
           let scope' = Equations.Scope.min (find_scope t1) (find_scope t2) in
           match acc with
           | None -> Some scope'
           | Some scope -> if scope' < scope then Some scope' else Some scope)


  let get_min_expansive ~(ctx : ctx) t =
    (* TODO: Come up w/ clever datastructure to compute this efficiently *)
    Hashtbl.fold
      t.rigid_vars
      ~init:None
      ~f:(fun ~key:rigid_var ~data:(is_expansive, rigid_var_scope) acc ->
        if not is_expansive
        then acc
        else (
          match acc, Equations.Ctx.get_equation (ectx ctx) rigid_var with
          | None, Some rigid_type ->
            Some ((rigid_var, rigid_var_scope), rigid_type)
          | Some (_, rigid_type), Some rigid_type'
            when snd rigid_type' < snd rigid_type ->
            Some ((rigid_var, rigid_var_scope), rigid_type')
          | _ -> acc))


  exception Cannot_decompose

  let decompose ~expansive ~ctx ~equate t1 t2 =
    (* In order to decompose 2 ambivalent types, we determine the common member 
       (if one exists) with the smallest "scope" to decompose "on". *)
    (* There are 2 rules for decomposition of ambivalent types:
       - decomposing on the structure
       - decomposing via a common rigid variable *)
    match find_decomposable_rigid_var_scope t1 t2 with
    | Some scope ->
      (* We can decompose on the common rigid var [rigid_var] between [t1] 
         and [t2]. *)
      (* From [find_decomposable_rigid_var], we know that [scope] the minimum
         scope for a common rigid variable. *)
      let scope =
        Equations.Scope.max t1.scope t2.scope |> Equations.Scope.max scope
      in
      let structure = merge_structure t1 t2 in
      let rigid_vars = merge_rigid_vars t1 t2 in
      { structure; rigid_vars; scope }
    | None ->
      (* If there is no-common rigid variable, then we attempt to decompose on the 
         structure *)
      (match Option.both t1.structure t2.structure with
      | None -> raise Cannot_decompose
      | Some (structure1, structure2) ->
        (* Determine the merged structure *)
        let structure =
          merge_scoped
            structure1
            structure2
            ~f:
              (Structure.merge
                 ~expansive:expansive.sexpansive
                 ~ctx:(sctx ctx)
                 ~equate)
        in
        (* Compute the required scope for the decomposition. *)
        let scope =
          Equations.Scope.max t1.scope t2.scope
          |> Equations.Scope.max (decompose_scope structure1 structure2)
        in
        (* Merge the rigid variables *)
        let rigid_vars = merge_rigid_vars t1 t2 in
        { structure = Some structure; scope; rigid_vars })


  exception Cannot_expand




  let expand ~expansive ~(ctx : ctx) t1 t2 =
    (* We first must determine which ambivalence we will
       be expanding. *)
    let t, (rigid_var, rigid_type) =
      match get_min_expansive ~ctx t1, get_min_expansive ~ctx t2 with
      | None, None -> raise Cannot_expand
      | Some expansive, None -> t1, expansive
      | None, Some expansive -> t2, expansive
      | ( Some ((_, rigid_type1) as expansive1)
        , Some ((_, rigid_type2) as expansive2) ) ->
        if snd rigid_type1 < snd rigid_type2
        then t1, expansive1
        else t2, expansive2
    in
    (* We now add [rigid_type] to [t]. *)
    (match fst rigid_type with
    | Rigid_type.Rigid_var rigid_var' ->
      (* Add [rigid_var'] to [rigid_vars] w/ the scope of the equation. *)
      (match
         Hashtbl.add t.rigid_vars ~key:rigid_var' ~data:(true, snd rigid_type)
       with
      | `Ok | `Duplicate -> ())
    | Rigid_type.Structure structure ->
      (match t.structure with
      | Some _ -> ()
      | None ->
        (* Convert [structure] using [term]. *)
        let structure =
          Structure.map structure ~f:(convert_rigid_type ~make:expansive.make)
        in
        t.structure <- Some (structure, snd rigid_type)));
    (* Set [rigid_var]  to be non-expansive *)
    Hashtbl.set t.rigid_vars ~key:(fst rigid_var) ~data:(false, snd rigid_var)


  let is_variable t =
    Option.is_none t.structure && Hashtbl.is_empty t.rigid_vars *)

  (* let merge ~expansive ~(ctx : ctx) ~equate t1 t2 =
    if is_variable t1
    then t2
    else if is_variable t2
    then t1
    else (
      let rec loop () =
        try decompose ~expansive ~ctx ~equate t1 t2 with
        | Structure.Cannot_merge -> raise Cannot_merge
        | Cannot_decompose ->
          (try expand ~expansive ~ctx t1 t2 with
          | Cannot_expand -> raise Cannot_merge);
          loop ()
      in
      loop ()) *)
end