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
open Structure

module Make (Algebra : Algebra) = struct
  open Algebra
  module Constraint = Constraint.Make (Algebra)
  module Type_var = Types.Var
  module Type_former = Types.Former
  module Type = Types.Type

  (* Aliases *)
  module C = Constraint
  module G = Generalization.Make (Types.Label) (Type_former)
  module U = G.Unifier

  (* Abbreviation exports *)

  module Abbrev_type = G.Abbrev_type
  module Abbreviations = G.Abbreviations

  (* Ambivalent exports *)

  module Equations = G.Equations

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
    let[@landmark] decode_variable var =
      Log.debug (fun m -> m "Decode variable");
      Type_var.of_int (U.Type.id var)


    let[@landmark] decode_rigid_variable (rigid_var : Rigid_var.t) =
      Type_var.of_int (rigid_var :> int)


    (* [decode_type type_] decodes type [type_] (may contain cycles) into a [Type]. 
       Cache is causing wierd segfault. TODO investigate more...
    *)
    (* let decode_type : t =
      let cache = Hashtbl.create ~size:30 (module U.Type) in
      fun type_ ->
        Log.debug (fun m -> m "Decoding type");
        try
          Log.debug (fun m -> m "Finding type in cache...");
          let type_ = Hashtbl.find_exn cache type_ in
          Log.debug (fun m -> m "Found type :)");
          type_
        with
        | Not_found_s _ ->
          Log.debug (fun m -> m "Failed to find type in cache, folding now...");
          let decoded_type =
            U.Type.fold
              ~f:(fun type_ structure ->
                match G.Structure.repr structure with
                | Flexible_var -> Type.var (decode_variable type_)
                | Rigid_var rigid_var ->
                  Type.var (decode_rigid_variable rigid_var)
                | Row_cons (label, label_type, tl) ->
                  Type.row_cons (label, label_type) tl
                | Row_uniform type_ -> Type.row_uniform type_
                | Former former -> Type.former former)
              ~var:(fun type_ -> Type.var (decode_variable type_))
              ~mu:(fun v t -> Type.mu (decode_variable v) t)
              type_
          in
          Hashtbl.set cache ~key:type_ ~data:decoded_type;
          decoded_type [@landmark "decode_type"] *)

    let decode_type : t =
     fun type_ ->
      Log.debug (fun m -> m "[decode_type] Decoding type %d" (U.Type.id type_));
      let decoded_type =
        U.Type.fold
          ~f:(fun type_ structure ->
            Log.debug (fun m -> m "[decode_type] executing f");
            match G.Structure.repr structure with
            | Flexible_var -> Type.var (decode_variable type_)
            | Rigid_var rigid_var -> Type.var (decode_rigid_variable rigid_var)
            | Row_cons (label, label_type, tl) ->
              Type.row_cons (label, label_type) tl
            | Row_uniform type_ -> Type.row_uniform type_
            | Former former -> Type.former former)
          ~var:(fun type_ -> Type.var (decode_variable type_))
          ~mu:(fun v t -> Type.mu (decode_variable v) t)
          type_
      in
      Log.debug (fun m -> m "Decoded type");
      decoded_type


    (* [decode_scheme scheme] decodes the graphical scheme [scheme] into a [Type.scheme]. *)
    let[@landmark] decode_scheme scheme =
      Log.debug (fun m -> m "Decoding scheme");
      ( List.map (G.variables scheme) ~f:decode_variable
      , decode_type (G.root scheme) )
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
    | Rigid_var of Rigid_var.t
    | Type of U.Type.t

  (* [make_state ()] returns a fresh solver state. *)
  let make_state abbrev_ctx =
    { generalization_state = G.make_state abbrev_ctx
    ; constraint_var_env = Hashtbl.create (module Int)
    }


  let[@landmark] enter state = G.enter ~state:state.generalization_state

  (* [exit state ~rigid_vars ~types] generalizes the types [types], returning
     the generalized variables and schemes. 
     
     Raises [Rigid_variable_escape] if a rigid variable from [rigid_vars] escapes.
     Raises [Scope_escape] if a type escapes it's equational scope 
  *)
  exception Rigid_variable_escape of Type_var.t
  exception Cannot_flexize of Type_var.t
  exception Scope_escape of Type.t

  let[@landmark] exit state ~rigid_vars ~types =
    try G.exit ~state:state.generalization_state ~rigid_vars ~types with
    | G.Scope_escape type_ -> raise (Scope_escape (Decoder.decode_type type_))
    | G.Rigid_variable_escape rigid_var ->
      raise (Rigid_variable_escape (Decoder.decode_rigid_variable rigid_var))
    | G.Cannot_flexize rigid_var ->
      raise (Cannot_flexize (Decoder.decode_rigid_variable rigid_var))


  (* [find state var] returns the corresponding graphical type of [var],
     mapped to by [state.constraint_var_env]. 
     
     Raises [Unbound_constraint_variable] if [var] is not in 
     [state.constraint_var_env]. *)
  exception Unbound_constraint_variable of C.variable

  let[@landmark] find state (var : C.variable) =
    match Hashtbl.find state.constraint_var_env (var :> int) with
    | None -> raise (Unbound_constraint_variable var)
    | Some (Rigid_var rigid_var) ->
      G.make_rigid_var ~state:state.generalization_state rigid_var
    | Some (Type type_) -> type_


  (* [bind state var type_] binds [type_] to the constraint variable [var] in 
     the environment. *)
  let[@landmark] bind state (var : C.variable) type_ =
    Hashtbl.set state.constraint_var_env ~key:(var :> int) ~data:type_


  let[@landmark] convert_shallow_type state shallow_type =
    let open C.Shallow_type in
    match shallow_type with
    | Former former ->
      G.make_former
        ~state:state.generalization_state
        (Type_former.map former ~f:(find state)) [@landmark "make_former"]
    | Row_cons (label, t1, t2) ->
      G.make_row_cons
        ~state:state.generalization_state
        ~label
        ~field:(find state t1)
        ~tl:(find state t2)
    | Row_uniform t ->
      G.make_row_uniform ~state:state.generalization_state (find state t)
    | Mu t -> find state t
    | Let t -> find state t


  (* [bind_flexible state (var, former_opt)] binds the flexible binding 
     (var, former_opt) in the environment. 
       
     Returning the graphical type mapped in the environment. *)
  let[@landmark] bind_flexible state var =
    let type_ = G.make_flexible_var ~state:state.generalization_state in
    bind state var (Type type_);
    type_


  (* [bind_rigid state var] binds the rigid variable [var] in the environment. 
     Returning the graphical type mapped in the environment. *)
  let[@landmark] bind_rigid state var =
    let rigid_var = Rigid_var.make () in
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
      { term_var_env :
          (Term_var.t, G.scheme, Term_var_comparator.comparator_witness) Map.t
      ; abbrev_ctx : Abbreviations.t
      ; equations_ctx : Equations.t
      }

    let empty abbrev_ctx =
      { term_var_env = Map.empty (module Term_var_comparator)
      ; abbrev_ctx
      ; equations_ctx = Equations.empty
      }


    (* TODO: Move to different env w/out abbrev_ctx and equations *)
    let merge t1 t2 =
      let term_var_env =
        Map.merge_skewed
          t1.term_var_env
          t2.term_var_env
          ~combine:(fun ~key:_ _ scheme -> scheme)
      in
      (* Arbitraryly chose [t1] abbrev_ctx and equation_ctx *)
      { term_var_env
      ; abbrev_ctx = t1.abbrev_ctx
      ; equations_ctx = t2.equations_ctx
      }


    let[@landmark] extend t var scheme =
      { t with term_var_env = Map.set t.term_var_env ~key:var ~data:scheme }


    let[@landmark] extend_types t var_type_alist =
      List.fold_left var_type_alist ~init:t ~f:(fun t (var, type_) ->
          let scheme = G.mono_scheme type_ in
          extend t var scheme)


    let[@landmark] extend_bindings state t bindings =
      extend_types t (List.map bindings ~f:(fun (x, a) -> x, find state a))


    exception Unbound_term_variable of Term_var.t

    let[@landmark] find t var =
      match Map.find t.term_var_env var with
      | Some scheme -> scheme
      | None -> raise (Unbound_term_variable var)


    let ctx t : G.Unifier.ctx =
      { abbrev_ctx = t.abbrev_ctx; equations_ctx = t.equations_ctx }


    let[@landmark] add_equation state t (rigid_type1, rigid_type2) =
      { t with
        equations_ctx =
          G.Equations.add
            ~state:state.generalization_state
            ~abbrev_ctx:t.abbrev_ctx
            t.equations_ctx
            rigid_type1
            rigid_type2
      }


    let[@landmark] add_equations state t equations =
      List.fold_left equations ~init:t ~f:(fun t equation ->
          add_equation state t equation)
  end

  exception Invalid_rigid_type

  let rec utype_to_rigid_type state type_ : G.Rigid_type.t =
    match G.Structure.repr (U.Type.structure type_) with
    | Rigid_var rigid_var -> G.Rigid_type.make_rigid_var rigid_var
    | Former former ->
      G.Rigid_type.make_former
        (Type_former.map former ~f:(utype_to_rigid_type state))
    | _ -> raise Invalid_rigid_type


  let rec ctype_to_rigid_type state type_ : G.Rigid_type.t =
    match (type_ : C.Type.t) with
    | Var x ->
      (match Hashtbl.find state.constraint_var_env (x :> int) with
      | None -> raise (Unbound_constraint_variable x)
      | Some (Rigid_var rigid_var) -> G.Rigid_type.make_rigid_var rigid_var
      | Some (Type type_) -> utype_to_rigid_type state type_)
    | Former former ->
      G.Rigid_type.make_former
        (Type_former.map former ~f:(ctype_to_rigid_type state))
    | _ -> raise Invalid_rigid_type


  exception Non_rigid_equations

  let[@landmark] add_equations ~state ~env equations =
    let equations =
      try
        List.map equations ~f:(fun (t1, t2) ->
            ctype_to_rigid_type state t1, ctype_to_rigid_type state t2)
      with
      | Invalid_rigid_type -> raise Non_rigid_equations
    in
    Env.add_equations state env equations


  (* [unify type1 type2] unifies [type1] and [type2], raising [Unify] is the 
     types cannot be unified. 
     
     The decoded types are now supplied in the exception [Unify]. 
  *)

  exception Unify of Type.t * Type.t

  let unify ~state ~env type1 type2 =
    try
      (* Log.debug (fun m -> m "Unify method in solve :)"); *)
      let to_string t =
        Decoder.decode_type t 
        |> Type.sexp_of_t
        |> Sexp.to_string_hum
      in
      Log.debug (fun m -> m "Unify\n %s \n%s" (to_string type1) (to_string type2));
      U.unify
        ~state:state.generalization_state
        ~ctx:(Env.ctx env)
        type1
        type2 [@landmark "unify"]
    with
    | U.Unify (type1, type2) ->
      raise (Unify (Decoder.decode_type type1, Decoder.decode_type type2))


  let[@landmark] bind_existential_ctx state (vars, bindings) =
    (* TODO: Optimize! *)
    List.iter vars ~f:(fun var -> ignore (bind_flexible state var : U.Type.t));
    let unify = unify ~state ~env:(Env.empty Abbreviations.empty) in
    List.iter bindings ~f:(fun (var, shallow_type) ->
        unify (find state var) (convert_shallow_type state shallow_type))


  type 'a let_rec_poly_binding =
    | Polymorphic of
        { universal_context : Constraint.universal_context
        ; annotation : Constraint.Shallow_type.encoded_type
        ; term_var : Term_var.t
        ; in_ : 'a Constraint.t
        }

  type 'a let_rec_mono_binding =
    | Monomorphic of
        { universal_context : Constraint.universal_context
        ; existential_context : Constraint.existential_context
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
      | Return x -> return x
      | True -> return ()
      | Map (cst, f) ->
        let value = solve ~state ~env cst in
        map value ~f
      | Conj (cst1, cst2) ->
        let value1 = solve ~state ~env cst1 in
        let value2 = solve ~state ~env cst2 in
        both value1 value2
      | Eq (a, a') ->
        Log.debug (fun m -> m "Solving [Eq].");
        unify ~state ~env (find state a) (find state a');
        return ()
      | Exist (ctx, cst) ->
        Log.debug (fun m -> m "Solving [Exist].");
        bind_existential_ctx state ctx;
        let value = solve ~state ~env cst in
        fun () ->
          Log.debug (fun m -> m "Elab Exist");
          value ()
      | Forall (ctx, cst) ->
        Log.debug (fun m -> m "Solving [Forall].");
        (* Enter a new region *)
        enter state;
        (* Introduce the rigid variables *)
        let rigid_vars = List.map ~f:(bind_rigid state) ctx in
        (* Solve the constraint *)
        let value = solve ~state ~env cst in
        (* Generalize and exit *)
        ignore (exit state ~rigid_vars ~types:[] : G.variables * G.scheme list);
        fun () ->
          Log.debug (fun m -> m "Elab Forall");
          value ()
      | Def (bindings, in_) ->
        Log.debug (fun m -> m "Solving [Def].");
        let env = Env.extend_bindings state env bindings in
        let value = solve ~state ~env in_ in
        fun () ->
          Log.debug (fun m -> m "Elab Def");
          value ()
      | Instance (x, a) ->
        Log.debug (fun m -> m "Solving [Instance].");
        let scheme = Env.find env x in
        let instance_variables, type_ =
          (G.instantiate
             ~state:state.generalization_state
             scheme [@landmark "instantiate"])
        in
        unify ~state ~env (find state a) type_;
        fun () ->
          Log.debug (fun m -> m "Elab Instance");
          List.map ~f:Decoder.decode_type instance_variables
      | Let (let_bindings, cst) ->
        Log.debug (fun m -> m "Solving [Let]");
        let term_let_bindings, env, equations =
          solve_let_bindings ~state ~env let_bindings
        in
        enter state;
        let env = Env.add_equations state env equations in
        let value = solve ~state ~env cst in
        ignore
          (exit state ~rigid_vars:[] ~types:[] : G.variables * G.scheme list);
        fun () ->
          Log.debug (fun m -> m "Elab Let");
          both term_let_bindings value ()
      | Let_rec (let_rec_bindings, cst) ->
        Log.debug (fun m -> m "Solving [Let_rec]");
        let term_let_rec_bindings, env =
          solve_let_rec_bindings ~state ~env let_rec_bindings
        in
        let value = solve ~state ~env cst in
        fun () ->
          Log.debug (fun m -> m "Elab Let_rec");
          both term_let_rec_bindings value ()
      | Decode a ->
        let var = find state a in
        fun () ->
          Log.debug (fun m -> m "Elab Decode");
          Decoder.decode_type var
      | Implication (equations, t) ->
        Log.debug (fun m -> m "Solving [Implication].");
        (* Enter a new scope (region) *)
        enter state;
        (* Add equations *)
        let env = add_equations ~env ~state equations in
        (* Solve [t] w/ new equations *)
        let value = solve ~state ~env t in
        (* Exit region *)
        ignore
          (exit state ~rigid_vars:[] ~types:[] : G.variables * G.scheme list);
        fun () ->
          Log.debug (fun m -> m "Elab Implication");
          value ()


  and[@landmark] solve_let_binding
      : type a.
        state:state
        -> env:Env.t
        -> a Constraint.let_binding
        -> a Constraint.term_let_binding Elaborate.t
           * Env.t
           * (G.Rigid_type.t * G.Rigid_type.t) list
    =
   fun ~state
       ~env
       (Let_binding
         { universal_context
         ; existential_context
         ; is_non_expansive
         ; bindings
         ; in_
         ; equations
         }) ->
    (* Enter a new region *)
    if is_non_expansive then enter state;
    (* Initialize fresh flexible and rigid variables *)
    let rigid_vars =
      if is_non_expansive
      then List.map ~f:(bind_rigid state) universal_context
      else []
    in
    bind_existential_ctx state existential_context;
    (* Convert the constraint types into graphic types *)
    let types = List.map bindings ~f:(fun (_, a) -> find state a) in
    (* Solve the constraint of the let binding *)
    let value = solve ~state ~env in_ in
    (* Convert equations to rigid equations. *)
    let equations =
      try
        List.map equations ~f:(fun (t1, t2) ->
            ctype_to_rigid_type state t1, ctype_to_rigid_type state t2)
      with
      | Invalid_rigid_type -> raise Non_rigid_equations
    in
    (* Generalize and exit *)
    let generalizable, schemes =
      if is_non_expansive
      then exit state ~rigid_vars ~types
      else [], List.map types ~f:G.mono_scheme
    in
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
        Log.debug (fun m -> m "Elab Let binding");
        ( List.map ~f:(fun (var, sch) -> var, Decoder.decode_scheme sch) bindings
        , (List.map ~f:Decoder.decode_variable generalizable, value ()) ))
    , env
    , equations )


  and solve_let_bindings
      : type a.
        state:state
        -> env:Env.t
        -> a Constraint.let_binding list
        -> a Constraint.term_let_binding list Elaborate.t
           * Env.t
           * (G.Rigid_type.t * G.Rigid_type.t) list
    =
   fun ~state ~env let_bindings ->
    let term_let_bindings, env, equations =
      List.fold_right
        let_bindings
        ~f:(fun let_binding (term_let_bindings, env, equations) ->
          let term_let_binding, env, equations' =
            solve_let_binding ~state ~env let_binding
          in
          term_let_binding :: term_let_bindings, env, equations' @ equations)
        ~init:([], env, [])
    in
    Elaborate.list term_let_bindings, env, equations


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
      Log.debug (fun m -> m "Computing polymorphic bindings of [Let_rec_poly]");
      (* Compute the type schemes for the polymorphic bindings *)
      let schemes =
        List.map
          let_rec_poly_bindings
          ~f:(fun
               (Polymorphic
                 { universal_context; annotation = existential_context, a; _ })
             ->
            (* Enter a new region to generalize annotation *)
            enter state;
            (* Initialize rigid variables and the annotation *)
            let rigid_vars = List.map ~f:(bind_rigid state) universal_context in
            (* Lookup the bound type *)
            let type_ =
              bind_existential_ctx state existential_context;
              find state a
            in
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
          ~f:(fun (env, bindings) (Polymorphic { term_var; _ }) scheme ->
            Env.extend env term_var scheme, (term_var, scheme) :: bindings)
      in
      Log.debug (fun m -> m "Solving [Let_rec_mono] bindings");
      let term_let_mono_bindings, env = k ~state ~env in
      (* We now assert the constraints in the polymorphic bindings *)
      Log.debug (fun m ->
          m "Checking [Let_rec_poly] bindings are correctly annotated.");
      let values =
        List.map
          let_rec_poly_bindings
          ~f:(fun
               (Polymorphic
                 { in_
                 ; universal_context
                 ; annotation = existential_context, _
                 ; _
                 })
             ->
            enter state;
            let rigid_vars = List.map ~f:(bind_rigid state) universal_context in
            bind_existential_ctx state existential_context;
            let value = solve ~state ~env in_ in
            let generalizable, _ = exit state ~rigid_vars ~types:[] in
            generalizable, value)
      in
      let make_term_let_rec_binding (var, scheme) (generalizable, value)
          : _ term_let_rec_binding Elaborate.t
        =
       fun () ->
        Log.debug (fun m -> m "Elab let rec poly");
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
      let rigid_vars =
        List.map
          let_rec_mono_bindings
          ~f:(fun (Monomorphic { universal_context; _ }) -> universal_context)
        |> List.concat
        |> List.map ~f:(bind_rigid state)
      in
      List.iter
        let_rec_mono_bindings
        ~f:(fun (Monomorphic { existential_context; _ }) ->
          bind_existential_ctx state existential_context);
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
        Log.debug (fun m -> m "Elab let rec mono");
        ( (var, Decoder.decode_scheme scheme)
        , ( List.map generalizable ~f:Decoder.decode_variable
          , (Log.debug (fun m -> m "Elab let rec mono value");
             let v = value () in
             Log.debug (fun m -> m "Elab let rec mono value after");
             v) ) )
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
            | Let_rec_mono_binding
                { universal_context; existential_context; binding; in_ } ->
              Either.First
                (Monomorphic
                   { universal_context; existential_context; binding; in_ })
            | Let_rec_poly_binding
                { universal_context; annotation; term_var; in_ } ->
              Either.Second
                (Polymorphic { universal_context; annotation; term_var; in_ }))
      in
      solve_let_rec_poly_bindings ~state ~env poly ~k:(fun ~state ~env ->
          solve_let_rec_mono_bindings ~state ~env mono)


  type error =
    [ `Unify of Type.t * Type.t
    | `Cycle of Type.t
    | `Unbound_term_variable of Term_var.t
    | `Unbound_constraint_variable of Constraint.variable
    | `Rigid_variable_escape of Type_var.t
    | `Cannot_flexize of Type_var.t
    | `Scope_escape of Type.t
    | `Non_rigid_equations
    | `Inconsistent_equations
    ]

  let init_logs ~debug:debug_flag =
    Logs.set_reporter reporter;
    Logs.Src.set_level src Logs.(if debug_flag then Some Debug else Some Info)


  let with_result ~f t : (_, [> error ]) Result.t =
    try Ok (f t) with
    | Unify (t1, t2) -> Error (`Unify (t1, t2))
    | Rigid_variable_escape a -> Error (`Rigid_variable_escape a)
    | Cannot_flexize a -> Error (`Cannot_flexize a)
    | Scope_escape t -> Error (`Scope_escape t)
    | Env.Unbound_term_variable x -> Error (`Unbound_term_variable x)
    | Unbound_constraint_variable a -> Error (`Unbound_constraint_variable a)
    | Non_rigid_equations -> Error `Non_rigid_equations
    | G.Equations.Inconsistent -> Error `Inconsistent_equations


  let solve ?(debug = false) ~abbrevs =
    init_logs ~debug;
    with_result ~f:(fun cst ->
        let[@landmark] solved =
          solve ~state:(make_state ()) ~env:(Env.empty abbrevs) cst
        in
        (Elaborate.run solved [@landmark "elaborate"]))


  module Structure = struct
    open Constraint.Structure

    module Item = struct
      let solve_let_bindings
          ~state
          ~env
          (let_bindings : _ Item.let_binding list)
        =
        let let_bindings =
          let_bindings
          |> List.map
               ~f:(fun
                    Item.
                      { universal_context
                      ; existential_context
                      ; is_non_expansive
                      ; bindings
                      ; in_
                      }
                  ->
                 Constraint.Binding.let_
                   ~ctx:(universal_context, existential_context)
                   ~is_non_expansive
                   ~bindings
                   ~in_
                   ~equations:[])
        in
        let let_bindings, env, equations =
          solve_let_bindings ~state ~env let_bindings
        in
        assert (List.is_empty equations);
        let_bindings, env


      let rec solve
          : type a.
            state:state -> env:Env.t -> a Item.t -> a Elaborate.t * Env.t
        =
        let open Item in
        let open Elaborate in
        fun ~state ~env t ->
          match t with
          | Return x -> return x, env
          | Map (t, f) ->
            let value, env = solve ~state ~env t in
            map value ~f, env
          | Both (t1, t2) ->
            let value1, env1 = solve ~state ~env t1 in
            let value2, env2 = solve ~state ~env t2 in
            both value1 value2, Env.merge env1 env2
          | Let let_bindings ->
            Log.debug (fun m ->
                m
                  "Solving let bindings: %s"
                  ([%sexp (let_bindings : let_binding list)]
                  |> Sexp.to_string_hum));
            solve_let_bindings ~state ~env let_bindings
          | Def bindings ->
            let env = Env.extend_bindings state env bindings in
            return (), env
          | Let_rec let_rec_bindings ->
            solve_let_rec_bindings ~state ~env let_rec_bindings
    end

    (* Would require new type for modules: 
        type 'a t = 
          { structure: 'a 
          ; env : Env.t 
          } *)

    let solve : type a. state:state -> env:Env.t -> a t -> a list Elaborate.t =
     fun ~state ~env t ->
      (* Enter a new region *)
      enter state;
      let _env, values =
        List.fold_left t ~init:(env, []) ~f:(fun (env, values) item ->
            let value, env = Item.solve ~state ~env item in
            env, value :: values)
      in
      (* Generalize and exit *)
      ignore (exit state ~rigid_vars:[] ~types:[] : G.variables * G.scheme list);
      Elaborate.list (List.rev values)


    let solve ?(debug = false) ~abbrevs =
      init_logs ~debug;
      with_result ~f:(fun t ->
          let[@landmark] solved =
            solve ~state:(make_state ()) ~env:(Env.empty abbrevs) t
          in
          Log.debug (fun m -> m "Starting elaboration");
          Elaborate.run solved [@landmark "elaborate-structure"])
  end
end

module Private = struct
  module Structure = Structure
  module Generalization = Generalization.Make
  module Unifier = Unifier.Make
  module Union_find = Union_find
end
