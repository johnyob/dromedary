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

(* This module implements a constraint solver and term elaborator, based on F.
   Pottier's paper ??. *)

open! Import

module Make (Algebra : Algebra) = struct
  open Algebra
  module Constraint = Constraint.Make (Algebra)
  module Type_var = Types.Var
  module Type_former = Types.Former
  module Type = Types.Type

  (* Aliases *)
  module C = Constraint
  module G = Generalization.Make (Type_former)
  module U = G.Unifier

  module Abbreviations = G.Abbreviations

  (* Applicative structure used for elaboration. *)

  module Elaborate = struct
    type 'a t = unit -> 'a

    let run t = t ()
    let return x () = x
    let map t ~f () = f (t ())
    let both t1 t2 () = t1 (), t2 ()
    let list : type a. a t list -> a list t = fun ts () -> List.map ts ~f:run

    let list_append : type a. a list t -> a list t -> a list t =
      fun ts1 ts2 () -> ts1 () @ ts2 ()
  end

  (* Type reconstruction requires the notion of "decoding" the efficient graphical types
     into the "tree-like" types defined by [Types].

     See F. Pottier's paper [??].
  *)

  module Decoder = struct
    type t = U.Type.t -> Type.t

    (* [decode_variable var] decodes [var] into a [Type_var] using it's unique identifier. *)
    let decode_variable var =
      assert (
        match U.Type.get_structure var with
        | U.Type.Flexible_var -> true
        | _ -> false);
      Type_var.of_int (U.Type.id var)

    let decode_rigid_variable rigid_var = 
      Type_var.of_int (U.Rigid_var.id rigid_var)

    (* [decode_type_acyclic type_] decodes type [type_] (known to have no cycles) into a [Type]. *)
    let decode_type_acyclic : t =
      G.fold_acyclic
        ~flexible_var:(fun v -> Type.var (decode_variable v))
        ~rigid_var:(fun v _ -> Type.var (decode_rigid_variable v))
        ~former:Type.former


    (* [decode_type_cyclic type_] decodes type [type_] (may contain cycles) into a [Type]. *)
    let decode_type_cyclic : t =
      G.fold_cyclic
        ~flexible_var:(fun v -> Type.var (decode_variable v))
        ~rigid_var:(fun v _ -> Type.var (decode_rigid_variable v))
        ~former:Type.former
        ~mu:(fun v t -> Type.mu (decode_variable v) t)


    (* [decode_scheme scheme] decodes the graphical scheme [scheme] into a [Type.scheme]. *)
    let decode_scheme scheme =
      ( List.map (G.variables scheme) ~f:decode_variable
      , decode_type_acyclic (G.root scheme) )
  end



  (* State.
      
     The solver state extends generalization state [G.state]
     with a environment ρ mapping constraint variables to graphical types.
  *)

  type state =
    { generalization_state : G.state
    ; constraint_var_env : (int, type_) Hashtbl.t
    }

  and type_ = 
    | Rigid_var of U.Rigid_var.t
    | Type of U.Type.t

  (* [make_state ()] returns a fresh solver state. *)
  let make_state abbrev_ctx =
    { generalization_state = G.make_state abbrev_ctx
    ; constraint_var_env = Hashtbl.create (module Int)
    }


  let enter state = G.enter state.generalization_state

  (* [unify type1 type2] unifies [type1] and [type2], raising [Unify] is the 
     types cannot be unified. 
     
     The decoded types are now supplied in the exception [Unify]. 
  *)

  exception Unify of Type.t * Type.t

  let unify state type1 type2 =
    try G.unify state.generalization_state type1 type2 with
    | U.Unify (type1, type2) ->
      raise
        (Unify
           (Decoder.decode_type_cyclic type1, Decoder.decode_type_cyclic type2))


  (* [exit state ~rigid_vars ~types] generalizes the types [types], returning
     the generalized variables and schemes. 
     
     Raises [Cycle] if a cycle occurs in [types] or 
     [Rigid_variable_escape] if a rigid variable from [rigid_vars] escapes. 
  *)
  exception Cycle of Type.t
  exception Rigid_variable_escape of Type_var.t
  exception Cannot_flexize of Type_var.t

  let exit state ~rigid_vars ~types =
    try G.exit state.generalization_state ~rigid_vars ~types with
    | U.Cycle type_ -> raise (Cycle (Decoder.decode_type_cyclic type_))
    | G.Rigid_variable_escape rigid_var ->
      raise (Rigid_variable_escape (Decoder.decode_rigid_variable rigid_var))
    | G.Cannot_flexize rigid_var ->
      raise (Cannot_flexize (Decoder.decode_rigid_variable rigid_var))
      


  (* [find state var] returns the corresponding graphical type of [var],
     mapped to by [state.constraint_var_env]. 
     
     Raises [Unbound_constraint_variable] if [var] is not in 
     [state.constraint_var_env]. 
  *)
  exception Unbound_constraint_variable of C.variable

  let find state (var : C.variable) =
    match Hashtbl.find state.constraint_var_env (var :> int) with
    | None -> raise (Unbound_constraint_variable var)
    | Some (Rigid_var rigid_var) -> G.make_rigid_var state.generalization_state rigid_var
    | Some (Type type_) -> type_


  (* [bind state var type_] binds [type_] to the constraint variable [var] in 
     the environment. *)
  let bind state (var : C.variable) type_ =
    Hashtbl.set state.constraint_var_env ~key:(var :> int) ~data:type_


  (* [bind_flexible state (var, former_opt)] binds the flexible binding 
     (var, former_opt) in the environment. 
     
     Returning the graphical type mapped in the environment. 
  *)
  let bind_flexible state (var, former_opt) =
    let type_ =
      match former_opt with
      | None -> G.make_flexible_var state.generalization_state
      | Some former ->
        G.make_former
          state.generalization_state
          (Type_former.map former ~f:(find state))
    in
    bind state var (Type type_);
    type_


  (* [bind_rigid state var] binds the rigid variable [var] in the environment. 
     Returning the graphical type mapped in the environment. *)
  let bind_rigid state var =
    let rigid_var = U.Rigid_var.make () in
    bind state var (Rigid_var rigid_var);
    rigid_var


  (* An environment in our constraint solver is defined as a partial finite
     function from term variables to schemes.

     We implement this using a [Map].

     We favor [Map] over [Hashtbl] here since we want immutability for recursive
     calls, as modifications in a local block shouldn't affect the overall
     environment

     e.g. let x : 'a ... 'b. [ let y : 'c ... 'd. [ C ] in C' ] in C'', here
     binding y shouldn't affect the environment for C''. This would not be the
     case for a mutable mapping (using side-effecting operations).

     Using [Hashtbl] would implement a dynamically scoped environment as opposed
     to a lexically scoped one. 
  *)

  module Env = struct
    module Term_var_comparator = struct
      type t = Term_var.t

      include Comparator.Make (Term_var)
    end

    type t =
      (Term_var.t, G.scheme, Term_var_comparator.comparator_witness) Map.t

    let empty = Map.empty (module Term_var_comparator)
    let extend t var scheme = Map.set t ~key:var ~data:scheme

    let extend_types t var_type_alist =
      List.fold_left var_type_alist ~init:t ~f:(fun t (var, type_) ->
          let scheme = G.mono_scheme type_ in
          extend t var scheme)


    let extend_bindings state t bindings =
      extend_types t (List.map bindings ~f:(fun (x, a) -> x, find state a))


    exception Unbound_term_variable of Term_var.t

    let find t var =
      match Map.find t var with
      | Some scheme -> scheme
      | None -> raise (Unbound_term_variable var)
  end

  type 'a let_rec_poly_binding =
    | Polymorphic of
        { rigid_vars : Constraint.variable list
        ; annotation_bindings : Constraint.Shallow_type.binding list
        ; binding : Constraint.binding
        ; in_ : 'a Constraint.t
        }

  type 'a let_rec_mono_binding =
    | Monomorphic of
        { rigid_vars : Constraint.variable list
        ; flexible_vars : Constraint.Shallow_type.binding list
        ; binding : Constraint.binding
        ; in_ : 'a Constraint.t
        }

  let rec solve
      : type a. state:state -> env:Env.t -> a Constraint.t -> a Elaborate.t
    =
    let open Constraint in
    let open Elaborate in
    fun ~state ~env cst ->
      match cst with
      | True -> return ()
      | Map (cst, f) ->
        let value = solve ~state ~env cst in
        map value ~f
      | Conj (cst1, cst2) ->
        both (solve ~state ~env cst1) (solve ~state ~env cst2)
      | Eq (a, a') ->
        unify state (find state a) (find state a');
        return ()
      | Exist (bindings, cst) ->
        ignore (List.map ~f:(bind_flexible state) bindings : U.Type.t list);
        solve ~state ~env cst
      | Forall (vars, cst) ->
        (* Enter a new region *)
        enter state;
        (* Introduce the rigid variables *)
        let rigid_vars = List.map ~f:(fun var -> bind_rigid state var) vars in
        (* Solve the constraint *)
        let value = solve ~state ~env cst in
        (* Generalize and exit *)
        ignore (exit state ~rigid_vars ~types:[] : G.variables * G.scheme list);
        value
      | Def (bindings, in_) ->
        let env = Env.extend_bindings state env bindings in
        solve ~state ~env in_
      | Instance (x, a) ->
        let scheme = Env.find env x in
        let instance_variables, type_ =
          G.instantiate state.generalization_state scheme
        in
        unify state (find state a) type_;
        fun () -> List.map ~f:Decoder.decode_type_acyclic instance_variables
      | Let (let_bindings, cst) ->
        let term_let_bindings, env =
          solve_let_bindings ~state ~env let_bindings
        in
        let value = solve ~state ~env cst in
        both term_let_bindings value
      | Let_rec (let_rec_bindings, cst) ->
        let term_let_rec_bindings, env =
          solve_let_rec_bindings ~state ~env let_rec_bindings
        in
        let value = solve ~state ~env cst in
        both term_let_rec_bindings value
      | Match (cst, cases) ->
        let value = solve ~state ~env cst in
        let case_values =
          List.map cases ~f:(fun (Case { bindings; in_ }) ->
              let env = Env.extend_bindings state env bindings in
              solve ~state ~env in_)
        in
        both value (list case_values)
      | Decode a -> fun () -> Decoder.decode_type_acyclic (find state a)


  and solve_let_binding
      : type a.
        state:state
        -> env:Env.t
        -> a Constraint.let_binding
        -> a Constraint.term_let_binding Elaborate.t * Env.t
    =
   fun ~state ~env (Let_binding { rigid_vars; flexible_vars; bindings; in_ }) ->
    (* Enter a new region *)
    G.enter state.generalization_state;
    (* Initialize fresh flexible and rigid variables *)
    let _flexible_vars = List.map ~f:(bind_flexible state) flexible_vars
    and rigid_vars = List.map ~f:(bind_rigid state) rigid_vars in
    (* Convert the constraint types into graphic types *)
    let types = List.map bindings ~f:(fun (_, a) -> find state a) in
    (* Solve the constraint of the let binding *)
    let value = solve ~state ~env in_ in
    (* Generalize and exit *)
    let generalizable, schemes = exit state ~rigid_vars ~types in
    (* Extend environment *)
    let env, bindings =
      List.zip_exn bindings schemes
      |> List.fold_left
           ~init:(env, [])
           ~f:(fun (env, bindings) ((var, _), scheme) ->
             Env.extend env var scheme, (var, scheme) :: bindings)
    in
    (* Return binding and extended environment *)
    ( (fun () ->
        ( List.map ~f:(fun (var, sch) -> var, Decoder.decode_scheme sch) bindings
        , (List.map ~f:Decoder.decode_variable generalizable, value ()) ))
    , env )


  and solve_let_bindings
      : type a.
        state:state
        -> env:Env.t
        -> a Constraint.let_binding list
        -> a Constraint.term_let_binding list Elaborate.t * Env.t
    =
   fun ~state ~env let_bindings ->
    let term_let_bindings, env =
      List.fold_right
        let_bindings
        ~f:(fun let_binding (term_let_bindings, env) ->
          let term_let_binding, env =
            solve_let_binding ~state ~env let_binding
          in
          term_let_binding :: term_let_bindings, env)
        ~init:([], env)
    in
    Elaborate.list term_let_bindings, env


  and solve_let_rec_poly_bindings
      : type a.
        state:state
        -> env:Env.t
        -> a let_rec_poly_binding list
        -> k:
             (state:state
              -> env:Env.t
              -> a Constraint.term_let_rec_binding list Elaborate.t * Env.t)
        -> a Constraint.term_let_rec_binding list Elaborate.t * Env.t
    =
    let open Constraint in
    (* Usage of continuation k is for an arbitrary context, used for the monomorphic bindings *)
    fun ~state ~env let_rec_poly_bindings ~k ->
      (* Compute the type schemes for the polymorphic bindings *)
      let schemes =
        List.map
          let_rec_poly_bindings
          ~f:(fun
               (Polymorphic
                 { rigid_vars; annotation_bindings; binding = _, a; _ })
             ->
            (* Enter a new region to generalize annotation *)
            enter state;
            (* Initialize rigid variables and the annotation *)
            let rigid_vars = List.map ~f:(bind_rigid state) rigid_vars
            and _annotation =
              List.map ~f:(bind_flexible state) annotation_bindings
            in
            (* Lookup the bound type *)
            let type_ = find state a in
            (* Generalize and exit *)
            let _generalizable, schemes =
              exit state ~rigid_vars ~types:[ type_ ]
            in
            (* TODO: Add assertion here: ensure generalizable = rigid_vars *)
            let scheme = List.hd_exn schemes in
            scheme)
      in
      (* Extend environment that binds the recursive polymorphic bindings *)
      let env, bindings =
        List.fold2_exn
          let_rec_poly_bindings
          schemes
          ~init:(env, [])
          ~f:(fun (env, bindings) (Polymorphic { binding = x, _; _ }) scheme ->
            Env.extend env x scheme, (x, scheme) :: bindings)
      in
      let term_let_mono_bindings, env = k ~state ~env in
      (* We now assert the constraints in the polymorphic bindings *)
      let values =
        List.map
          let_rec_poly_bindings
          ~f:(fun (Polymorphic { in_; rigid_vars; annotation_bindings; _ }) ->
            enter state;
            let rigid_vars = List.map ~f:(bind_rigid state) rigid_vars
            and _annotation_binding =
              List.map ~f:(bind_flexible state) annotation_bindings
            in
            let value = solve ~state ~env in_ in
            let generalizable, _ = exit state ~rigid_vars ~types:[] in
            generalizable, value)
      in
      let make_term_let_rec_binding (var, scheme) (generalizable, value)
          : _ term_let_rec_binding Elaborate.t
        =
       fun () ->
        ( (var, Decoder.decode_scheme scheme)
        , (List.map generalizable ~f:Decoder.decode_variable, value ()) )
      in
      ( Elaborate.list_append
          (List.map2_exn bindings values ~f:make_term_let_rec_binding
          |> Elaborate.list)
          term_let_mono_bindings
      , env )


  and solve_let_rec_mono_bindings
      : type a.
        state:state
        -> env:Env.t
        -> a let_rec_mono_binding list
        -> a Constraint.term_let_rec_binding list Elaborate.t * Env.t
    =
    let open Constraint in
    fun ~state ~env let_rec_mono_bindings ->
      (* Enter a new region. *)
      enter state;
      (* Initialize the fresh flexible and rigid variables for each of the bindings. *)
      let _flexible_vars =
        List.map
          let_rec_mono_bindings
          ~f:(fun (Monomorphic { flexible_vars; _ }) -> flexible_vars)
        |> List.concat
        |> List.map ~f:(bind_flexible state)
      and rigid_vars =
        List.map
          let_rec_mono_bindings
          ~f:(fun (Monomorphic { rigid_vars; _ }) -> rigid_vars)
        |> List.concat
        |> List.map ~f:(bind_rigid state)
      in
      (* Convert the constraint types into graphical types. *)
      let types =
        List.map
          let_rec_mono_bindings
          ~f:(fun (Monomorphic { binding = _, a; _ }) -> find state a)
      in
      (* The recursive environment binds the bindings from the [let_rec_bindings]. *)
      let rec_env =
        Env.extend_bindings
          state
          env
          (List.map
             ~f:(fun (Monomorphic { binding; _ }) -> binding)
             let_rec_mono_bindings)
      in
      (* Solve the values *)
      let values =
        List.map let_rec_mono_bindings ~f:(fun (Monomorphic { in_; _ }) ->
            solve ~state ~env:rec_env in_)
      in
      (* Generalize and exit *)
      let generalizable, schemes = exit state ~rigid_vars ~types in
      (* Compute extended environment and bindings. *)
      let env, bindings =
        List.zip_exn let_rec_mono_bindings schemes
        |> List.fold_left
             ~init:(env, [])
             ~f:(fun (env, bindings) (Monomorphic { binding = x, _; _ }, s) ->
               Env.extend env x s, (x, s) :: bindings)
      in
      let make_term_let_rec_binding (var, scheme) value
          : _ term_let_rec_binding Elaborate.t
        =
       fun () ->
        ( (var, Decoder.decode_scheme scheme)
        , (List.map generalizable ~f:Decoder.decode_variable, value ()) )
      in
      (* Return recursive bindings and extended environment *)
      ( List.map2_exn bindings values ~f:make_term_let_rec_binding
        |> Elaborate.list
      , env )


  and solve_let_rec_bindings
      : type a.
        state:state
        -> env:Env.t
        -> a Constraint.let_rec_binding list
        -> a Constraint.term_let_rec_binding list Elaborate.t * Env.t
    =
    let open Constraint in
    fun ~state ~env bindings ->
      (* Partition bindings into polymorphic and monomorphic bindings *)
      let mono, poly =
        List.partition_map bindings ~f:(fun binding ->
            match binding with
            | Let_rec_mono_binding { rigid_vars; flexible_vars; binding; in_ }
              ->
              Either.First
                (Monomorphic { rigid_vars; flexible_vars; binding; in_ })
            | Let_rec_poly_binding
                { rigid_vars; annotation_bindings; binding; in_ } ->
              Either.Second
                (Polymorphic { rigid_vars; annotation_bindings; binding; in_ }))
      in
      solve_let_rec_poly_bindings ~state ~env poly ~k:(fun ~state ~env ->
          solve_let_rec_mono_bindings ~state ~env mono)


  type error =
    [ `Unify of Type.t * Type.t
    | `Cycle of Type.t
    | `Unbound_term_variable of Term_var.t
    | `Unbound_constraint_variable of C.variable
    | `Rigid_variable_escape of Type_var.t
    | `Cannot_flexize of Type_var.t
    ]

  let solve ~ctx cst =
    (* Wrap exceptions raised by solving in a [Result] type. *)
    try
      Ok (Elaborate.run (solve ~state:(make_state ctx) ~env:Env.empty cst))
    with
    | Unify (t1, t2) -> Error (`Unify (t1, t2))
    | Cycle t -> Error (`Cycle t)
    | Rigid_variable_escape a -> Error (`Rigid_variable_escape a)
    | Cannot_flexize a -> Error (`Cannot_flexize a)
    | Env.Unbound_term_variable x -> Error (`Unbound_term_variable x)
    | Unbound_constraint_variable a -> Error (`Unbound_constraint_variable a)
end

module Private = struct
  module Generalization = Generalization.Make
  module Unifier = Unifier.Make
  module Union_find = Union_find
end
