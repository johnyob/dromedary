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
open Parsetree

let rec free_variables_of_core_type core_type =
  match core_type with
  | Ptyp_var x -> String.Set.singleton x
  | Ptyp_arrow (core_type1, core_type2) ->
    String.Set.union
      (free_variables_of_core_type core_type1)
      (free_variables_of_core_type core_type2)
  | Ptyp_constr (core_types, _) | Ptyp_tuple core_types ->
    List.map ~f:free_variables_of_core_type core_types |> String.Set.union_list


let occurs_check x core_type =
  String.Set.mem (free_variables_of_core_type core_type) x


module Equations = struct
  type t =
    { rigid_variables : String.Set.t
    ; equations : (core_type * core_type) list
    }
  [@@deriving sexp_of]

  let invariant t : unit =
    Invariant.invariant [%here] t [%sexp_of: t] (fun () ->
        (* Assert that all free variables of [t.equations] are bound in [t.rigid_variables] *)
        assert (
          List.map t.equations ~f:(fun (t1, t2) ->
              String.Set.union
                (free_variables_of_core_type t1)
                (free_variables_of_core_type t2))
          |> String.Set.union_list
          |> String.Set.is_subset ~of_:t.rigid_variables);
        (* Assert that all equations in [t.equations] are in solved form *)
        assert (
          List.for_all t.equations ~f:(function
              | Ptyp_var _, _ | _, Ptyp_var _ -> true
              | _ -> false));
        (* Assert that equations are not cyclic. *)
        assert (
          List.for_all t.equations ~f:(function
              | Ptyp_var _, Ptyp_var _ -> false
              | Ptyp_var x, t | t, Ptyp_var x -> not (occurs_check x t)
              | _ -> assert false)))


  let empty = { rigid_variables = String.Set.empty; equations = [] }

  let merge t1 t2 =
    invariant t1;
    invariant t2;
    let t =
      { rigid_variables = String.Set.union t1.rigid_variables t2.rigid_variables
      ; equations = t1.equations @ t2.equations
      }
    in
    invariant t;
    t


  let is_rigid_type t core_type =
    let rec loop core_type =
      match core_type with
      | Ptyp_var x -> String.Set.mem t.rigid_variables x
      | Ptyp_arrow (core_type1, core_type2) ->
        loop core_type1 && loop core_type2
      | Ptyp_constr (core_types, _) | Ptyp_tuple core_types ->
        List.for_all core_types ~f:loop
    in
    loop core_type


  (* Normalization ~>_E (from the paper) *)

  module Normalization = struct
    (* [compare_precision t1 t2] defines a total ordering on equations [t1 = t2]. *)
    let compare_precision core_type1 core_type2 =
      match core_type1, core_type2 with
      | Ptyp_var x, Ptyp_var x' -> String.compare x x'
      | Ptyp_var _, _ -> -1
      | _, Ptyp_var _ -> 1
      | _ -> assert false


    (* [equivalence_class t core_type] returns the equivalence class descriptor
       of [core_type] modulo the equations [t]. *)
    let equivalence_class t core_type =
      invariant t;
      let max_by_precision = Base.Comparable.max compare_precision in
      List.fold_left
        t.equations
        ~init:core_type
        ~f:(fun equiv_class (core_type1, core_type2) ->
          if equal_core_type core_type1 core_type
          then max_by_precision core_type2 equiv_class
          else if equal_core_type core_type2 core_type
          then max_by_precision core_type1 equiv_class
          else equiv_class)


    let rec normalize t core_type =
      invariant t;
      match core_type with
      | Ptyp_var _ ->
        let equiv_class = equivalence_class t core_type in
        if not (equal_core_type equiv_class core_type)
        then normalize t equiv_class
        else equiv_class
      | Ptyp_arrow (core_type1, core_type2) ->
        Ptyp_arrow (normalize t core_type1, normalize t core_type2)
      | Ptyp_constr (core_types, constr) ->
        Ptyp_constr (List.map core_types ~f:(normalize t), constr)
      | Ptyp_tuple core_types ->
        Ptyp_tuple (List.map core_types ~f:(normalize t))
  end

  let normalize = Normalization.normalize

  let is_equivalent t core_type1 core_type2 =
    invariant t;
    let normalize = normalize t in
    let ( =% ) core_type1 core_type2 =
      equal_core_type core_type1 core_type2
      || equal_core_type (normalize core_type1) (normalize core_type2)
    in
    let rec loop core_type1 core_type2 =
      match core_type1, core_type2 with
      | ( Ptyp_arrow (core_type11, core_type12)
        , Ptyp_arrow (core_type21, core_type22) ) ->
        loop core_type11 core_type21 && loop core_type12 core_type22
      | Ptyp_constr (core_types1, constr1), Ptyp_constr (core_types2, constr2)
        ->
        if String.equal constr1 constr2
        then (
          match List.for_all2 core_types1 core_types2 ~f:loop with
          | Ok result -> result
          | Unequal_lengths -> false)
        else false
      | Ptyp_tuple core_types1, Ptyp_tuple core_types2 ->
        (match List.for_all2 core_types1 core_types2 ~f:loop with
        | Ok result -> result
        | Unequal_lengths -> false)
      | _, _ -> core_type1 =% core_type2
    in
    loop core_type1 core_type2


  exception Inconsistent

  let rec add_equation t (core_type1, core_type2) =
    invariant t;
    let t =
      match core_type1, core_type2 with
      | ( Ptyp_arrow (core_type11, core_type12)
        , Ptyp_arrow (core_type21, core_type22) ) ->
        add_equation
          (add_equation t (core_type11, core_type21))
          (core_type12, core_type22)
      | Ptyp_constr (core_types1, constr1), Ptyp_constr (core_types2, constr2)
        ->
        if String.equal constr1 constr2
        then (
          match
            List.fold2
              core_types1
              core_types2
              ~init:t
              ~f:(fun t core_type1 core_type2 ->
                add_equation t (core_type1, core_type2))
          with
          | Ok t -> t
          | Unequal_lengths -> raise Inconsistent)
        else raise Inconsistent
      | Ptyp_tuple core_types1, Ptyp_tuple core_types2 ->
        (match
           List.fold2
             core_types1
             core_types2
             ~init:t
             ~f:(fun t core_type1 core_type2 ->
               add_equation t (core_type1, core_type2))
         with
        | Ok t -> t
        | Unequal_lengths -> raise Inconsistent)
      | _, _ ->
        if (not (is_equivalent t core_type1 core_type2))
           && is_rigid_type t core_type1
           && is_rigid_type t core_type2
        then (
          let core_type1 = Normalization.normalize t core_type1
          and core_type2 = Normalization.normalize t core_type2 in
          if match core_type1, core_type2 with
             (* Fails occurs check *)
             | Ptyp_var x, core_type | core_type, Ptyp_var x ->
               occurs_check x core_type
             (* Not in equational form! *)
             | _ -> true
          then raise Inconsistent;
          { t with equations = (core_type1, core_type2) :: t.equations })
        else t
    in
    invariant t;
    t


  let add_rigid_variables t rigid_variables =
    invariant t;
    let t =
      { t with
        rigid_variables = String.Set.union rigid_variables t.rigid_variables
      }
    in
    invariant t;
    t


  let rigid_variables t = t.rigid_variables
  let is_rigid_variable t x = String.Set.mem t.rigid_variables x
  let equations t = t.equations
end

let fresh_variable =
  let next = ref 0 in
  fun () ->
    let variable = !next in
    next := !next + 1;
    "_" ^ Int.to_string variable


(* Shapes (from the paper) *)

module Shape = struct
  type t = string list * core_type [@@deriving sexp_of]

  let invariant equations ((flexible_variables, core_type) as t) : unit =
    Invariant.invariant [%here] t [%sexp_of: t] (fun () ->
        Equations.invariant equations;
        let flexible_variables = String.Set.of_list flexible_variables in
        let rigid_variables = Equations.rigid_variables equations in
        (* Assert that [flexible_variables] and rigid variables of [equations] are disjoint. *)
        assert (String.Set.are_disjoint flexible_variables rigid_variables);
        (* Assert thart free variables of [core_type] are in [flexibile_variables or rigid_variables]. *)
        assert (
          free_variables_of_core_type core_type
          |> String.Set.is_subset
               ~of_:(String.Set.union flexible_variables rigid_variables)))


  let equal (_, core_type1) (_, core_type2) =
    equal_core_type core_type1 core_type2


  let is_equivalent equations ((_, core_type1) as t1) ((_, core_type2) as t2) =
    invariant equations t1;
    invariant equations t2;
    Equations.is_equivalent equations core_type1 core_type2


  let bottom () =
    let x = fresh_variable () in
    [ x ], Ptyp_var x


  let normalize equations ((flexible_variables, core_type) as t) =
    invariant equations t;
    let t = flexible_variables, Equations.normalize equations core_type in
    invariant equations t;
    t
end

module Unifier = struct
  module Substitution = struct
    type t = core_type String.Map.t

    let empty = String.Map.empty

    let find t x =
      match String.Map.find t x with
      | Some core_type -> core_type
      | None -> Ptyp_var x


    let singleton = String.Map.singleton
    let merge t1 t2 = Map.merge_skewed t1 t2 ~combine:(fun ~key:_ _ x -> x)

    (* These functions don't really belong here... but this is a prototype (and unlikely to be used) *)
    let rec apply t core_type =
      match core_type with
      | Ptyp_var x -> find t x
      | Ptyp_arrow (core_type1, core_type2) ->
        Ptyp_arrow (apply t core_type1, apply t core_type2)
      | Ptyp_constr (core_types, constr) ->
        Ptyp_constr (List.map ~f:(apply t) core_types, constr)
      | Ptyp_tuple core_types -> Ptyp_tuple (List.map ~f:(apply t) core_types)


    let compose t1 t2 = merge (Map.map t2 ~f:(apply t1)) t1

    let rename_shape (vars, core_type) =
      let alist = List.map vars ~f:(fun x -> x, fresh_variable ()) in
      let t =
        String.Map.of_alist_exn
          (List.map ~f:(fun (x, x') -> x, Ptyp_var x') alist)
      in
      List.map ~f:snd alist, apply t core_type


    let close_shape equations (_flexible_variables, core_type) =
      let flexible_variables =
        String.Set.diff
          (free_variables_of_core_type core_type)
          (Equations.rigid_variables equations)
      in
      rename_shape (String.Set.to_list flexible_variables, core_type)


    let apply_shape equations t (flexible_variables, core_type) =
      close_shape equations (flexible_variables, apply t core_type)
  end

  let unify equations core_type1 core_type2 =
    Equations.invariant equations;
    let is_rigid_variable x = Equations.is_rigid_variable equations x in
    let rec loop core_type1 core_type2 =
      if Equations.is_equivalent equations core_type1 core_type2
      then Substitution.empty
      else (
        match core_type1, core_type2 with
        | Ptyp_var x1, Ptyp_var x2 ->
          if is_rigid_variable x1 && is_rigid_variable x2
          then
            raise_s [%message "Coercion: Cannot unify distinct rigid variables"]
          else
            Substitution.merge
              (if is_rigid_variable x1
              then Substitution.empty
              else Substitution.singleton x1 core_type2)
              (if is_rigid_variable x2
              then Substitution.empty
              else Substitution.singleton x2 core_type1)
        | (Ptyp_var x, core_type | core_type, Ptyp_var x)
          when not (is_rigid_variable x || occurs_check x core_type1) ->
          Substitution.singleton x core_type
        | ( Ptyp_arrow (core_type11, core_type12)
          , Ptyp_arrow (core_type21, core_type22) ) ->
          let subst1 = loop core_type11 core_type21 in
          let subst2 =
            loop
              (Substitution.apply subst1 core_type12)
              (Substitution.apply subst1 core_type22)
          in
          Substitution.compose subst2 subst1
        | Ptyp_constr (core_types1, constr1), Ptyp_constr (core_types2, constr2)
          when String.equal constr1 constr2 ->
          let subst =
            List.fold2
              core_types1
              core_types2
              ~init:Substitution.empty
              ~f:(fun subst core_type1 core_type2 ->
                Substitution.compose
                  (loop
                     (Substitution.apply subst core_type1)
                     (Substitution.apply subst core_type2))
                  subst)
          in
          (match subst with
          | Ok subst -> subst
          | Unequal_lengths ->
            raise_s
              [%message "Coercion: Cannot unify constructors of unequal arity"])
        | Ptyp_tuple core_types1, Ptyp_tuple core_types2 ->
          let subst =
            List.fold2
              core_types1
              core_types2
              ~init:Substitution.empty
              ~f:(fun subst core_type1 core_type2 ->
                Substitution.compose
                  (loop
                     (Substitution.apply subst core_type1)
                     (Substitution.apply subst core_type2))
                  subst)
          in
          (match subst with
          | Ok subst -> subst
          | Unequal_lengths ->
            raise_s
              [%message "Coercion: Cannot unify tuple types of unequal length"])
        | _, _ -> raise_s [%message "Coercion: Cannot unify!"])
    in
    loop core_type1 core_type2


  let unify_shape
      equations
      ((_, core_type1) as shape1)
      ((_, core_type2) as shape2)
    =
    Equations.invariant equations;
    Shape.invariant equations shape1;
    Shape.invariant equations shape2;
    unify equations core_type1 core_type2


  let lub equations core_type1 core_type2 =
    let subst = unify equations core_type1 core_type2 in
    Substitution.apply subst core_type1


  let lub_shape equations shape1 shape2 =
    let subst = unify_shape equations shape1 shape2 in
    Substitution.apply_shape equations subst shape1
end

(* Pruning (from the paper) *)

let has_lub equations core_type1 core_type2 =
  try
    ignore (Unifier.lub equations core_type1 core_type2 : core_type);
    true
  with
  | _ -> false


let denotation equations core_type =
  List.fold_left
    (Equations.equations equations)
    ~init:[]
    ~f:(fun denotation (t1, t2) ->
      if has_lub equations core_type t1 || has_lub equations core_type t2
      then t1 :: t2 :: denotation
      else denotation)


let prune equations1 equations2 (_, core_type) =
  let rec loop core_type =
    (* Compute denotations under each set of equations *)
    let denotation1 = denotation equations1 core_type
    and denotation2 = denotation equations2 core_type in
    (* Determine whether [denotation1 >= denotation2], if so, then 
       we iterate (as we need the lub) *)
    if List.for_all ~f:(List.mem ~equal:equal_core_type denotation1) denotation2
    then (
      match core_type with
      | Ptyp_var x -> Ptyp_var x
      | Ptyp_arrow (t1, t2) -> Ptyp_arrow (loop t1, loop t2)
      | Ptyp_constr (ts, constr) -> Ptyp_constr (List.map ~f:loop ts, constr)
      | Ptyp_tuple ts ->
        Ptyp_tuple (List.map ~f:loop ts)
        (* Otherwise, we loose information, and return the most general type (a flexible variable) *))
    else Ptyp_var (fresh_variable ())
  in
  loop core_type


(* IBIS *)

open Ast_types
open Types

let infer_constant const : Shape.t =
  match const with
  | Const_int _ -> [], Ptyp_constr ([], "int")
  | Const_bool _ -> [], Ptyp_constr ([], "bool")
  | Const_unit -> [], Ptyp_constr ([], "unit")


let rec infer_fragment ~env ~equations pat pat_shape =
  match pat with
  | Ppat_any -> Ppat_any, ([], equations, String.Map.empty)
  | Ppat_var x -> Ppat_var x, ([], equations, String.Map.singleton x pat_shape)
  | Ppat_const const ->
    ignore
      (Unifier.unify_shape equations pat_shape (infer_constant const)
        : core_type String.Map.t);
    Ppat_const const, ([], equations, String.Map.empty)
  | Ppat_alias (pat, x) ->
    let pat, (betas, equations, bindings) =
      infer_fragment ~env ~equations pat pat_shape
    in
    ( Ppat_alias (pat, x)
    , (betas, equations, String.Map.add_exn bindings ~key:x ~data:pat_shape) )
  | Ppat_constraint (pat, pat_shape') ->
    let pat_shape' = Shape.normalize equations pat_shape' in
    let pat, fragment =
      infer_fragment
        ~env
        ~equations
        pat
        (lub_shape equations pat_shape pat_shape')
    in
    Ppat_constraint (pat, pat_shape'), fragment
  (* | Ppat_coerce (_pat, _pat_type1, _pat_type2) -> assert false
  | Ppat_tuple pats -> assert false
  | Ppat_construct (constr, pat_arg) ->
    let constr_alphas, constr_arg, constr_type, constr_constraints =
      inst_constr_decl constr
    in
    (* Check [pat_shape] unifies w/ [constr_type] *)
    let subst = Unifier.unify equations constr_type (Shape.to_type pat_shape) in
    (match pat_arg, constr_arg with
    | ( Some (betas, pat_arg)
      , Some
          { constructor_arg_betas = constr_betas
          ; constructor_arg_type = constr_arg
          } ) ->
      (* Construct new equation theory *)
      let equations = Equations.add_equation Equation.add_rigid_variables in
      assert false
    | None, None ->
      let equations =
        List.fold_left
          (Substitution.apply_constraints subst constr_constraints)
          ~init:equations
          ~f:Equations.add_equation
      in
      Ppat_construct (constr, None), ([], equations, String.Map.empty)
    | _, _ -> raise_s [%message "Pattern constructor argument mistmatch"]) *)
