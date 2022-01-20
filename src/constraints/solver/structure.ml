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


  type 'a term = { fold : 'a t -> 'a }
  
  exception Cannot_merge

  let merge ~term ~ctx ~equate t1 t2 =
    match t1, t2 with
    | Var, structure | structure, Var -> structure
    | Structure structure1, Structure structure2 ->
      let term : _ Structure.term =
        { fold = (fun structure -> Structure structure |> term.fold) }
      in
      (try
         Structure (Structure.merge ~term ~ctx ~equate structure1 structure2)
       with
      | Structure.Cannot_merge -> raise Cannot_merge)
end

module Ambivalent (Structure : S) = struct
  module Rigid_type = struct
    type t =
      | Rigid_var of Rigid_var.t
      | Structure of t Structure.t
  end

  module Equations = struct
    module Scope = struct
      type t = int

      let min = min
      let max = max
      let outermost_scope = 0
    end

    type 'a scoped = 'a * Scope.t

    module Ctx = struct
      type t =
        (Rigid_var.t, Rigid_type.t scoped, Rigid_var.comparator_witness) Map.t

      let empty = Map.empty (module Rigid_var)

      exception Inconsistent

      let add _t _rigid_type1 _rigid_type2 _scope = assert false
      let get_equation t rigid_var = Map.find t rigid_var
    end
  end

  type 'a t =
    { mutable structure : 'a Structure.t Equations.scoped option
    ; scope : Equations.Scope.t
    ; rigid_vars : (Rigid_var.t, bool Equations.scoped) Hashtbl.t
    }
  

  let make_rigid_var rigid_var =
    let rigid_vars = Hashtbl.create (module Rigid_var) in
    Hashtbl.set
      rigid_vars
      ~key:rigid_var
      ~data:(true, Equations.Scope.outermost_scope);
    { structure = None; scope = Equations.Scope.outermost_scope; rigid_vars }


  let make_structure structure =
    { structure =
        Option.(
          structure
          >>| fun structure -> structure, Equations.Scope.outermost_scope)
    ; scope = Equations.Scope.outermost_scope
    ; rigid_vars = Hashtbl.create (module Rigid_var)
    }


  let structure t = t.structure |> Option.map ~f:fst
  let scope t = t.scope
  let rigid_vars t = Hash_set.of_hashtbl_keys t.rigid_vars
  let update_scope t scope = if t.scope < scope then { t with scope } else t


  let sexp_of_t sexp_of_a t = 
    structure t |> Option.sexp_of_t (Structure.sexp_of_t sexp_of_a)

  let iter t ~f =
    Option.iter t.structure ~f:(fun (structure, _) ->
        Structure.iter structure ~f)


  let fold t ~f ~init =
    Option.fold t.structure ~init ~f:(fun init (structure, _) ->
        Structure.fold structure ~init ~f)


  let map t ~f =
    { t with
      structure =
        Option.map t.structure ~f:(fun (structure, scope) ->
            Structure.map structure ~f, scope)
    }


  type ctx = Equations.Ctx.t * Structure.ctx

  let ectx = fst
  let sctx = snd

  type 'a term = { fold : 'a t -> 'a }

  exception Cannot_merge

  let merge_scoped scoped1 scoped2 ~f =
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

  let decompose ~term ~ctx ~equate t1 t2 =
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
          let term : _ Structure.term =
            { fold =
                (fun structure -> make_structure (Some structure) |> term.fold)
            }
          in
          merge_scoped
            structure1
            structure2
            ~f:(Structure.merge ~term ~ctx:(sctx ctx) ~equate)
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

  let convert_rigid_type ~term rigid_type =
    let rec loop rigid_type =
      term.fold
        (match rigid_type with
        | Rigid_type.Rigid_var rigid_var -> make_rigid_var rigid_var
        | Rigid_type.Structure structure ->
          let structure = Structure.map structure ~f:loop in
          make_structure (Some structure))
    in
    loop rigid_type


  let expand ~term ~(ctx : ctx) t1 t2 =
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
        let structure = Structure.map structure ~f:(convert_rigid_type ~term) in
        t.structure <- Some (structure, snd rigid_type)));
    (* Set [rigid_var]  to be non-expansive *)
    Hashtbl.set t.rigid_vars ~key:(fst rigid_var) ~data:(false, snd rigid_var)


  let merge ~term ~(ctx : ctx) ~equate t1 t2 =
    let rec loop () =
      try decompose ~term ~ctx ~equate t1 t2 with
      | Structure.Cannot_merge -> raise Cannot_merge
      | Cannot_decompose ->
        (try expand ~term ~ctx t1 t2 with
        | Cannot_expand -> raise Cannot_merge);
        loop ()
    in
    loop ()
end