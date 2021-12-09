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

(* ------------------------------------------------------------------------- *)

module Make (Algebra : Algebra) = struct
  (* ----------------------------------------------------------------------- *)

  open Algebra
  module Constraint = Constraint.Make (Algebra)
  module Type_var = Types.Var
  module Type_former = Types.Former
  module Type = Types.Type

  (* Aliases *)
  module C = Constraint
  module G = Generalization.Make (Type_former)
  module U = G.Unifier

  (* ----------------------------------------------------------------------- *)

  (* ----------------------------------------------------------------------- *)

  (* Applicative structure used for elaboration. *)

  module Elaborate = struct
    type 'a t = unit -> 'a

    let run t = t ()
    let return x () = x
    let map t ~f () = f (t ())
    let both t1 t2 () = t1 (), t2 ()
    let list : type a. a t list -> a list t = fun ts () -> List.map ts ~f:run
  end

  (* ----------------------------------------------------------------------- *)

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
     to a lexically scoped one. *)

  module Env = struct
    module Term_var_comparator = struct
      type t = Term_var.t

      include Comparator.Make (Term_var)
    end

    type t =
      (Term_var.t, G.scheme, Term_var_comparator.comparator_witness) Map.t

    let empty = Map.empty (module Term_var_comparator)
    let extend t var sch = Map.add_exn t ~key:var ~data:sch
    let find t var = Map.find_exn t var

    let extends_typs t bindings =
      List.fold_left bindings ~init:t ~f:(fun t (var, typ) ->
          let sch = G.monoscheme typ in
          extend t var sch)
  end

  (* ----------------------------------------------------------------------- *)

  (* Decoding types (from F. Pottier's paper ??) *)

  type decoder = U.Type.t -> Types.Type.t

  let decode_variable typ = Type_var.of_int (U.Type.id typ)

  let decode : decoder =
    U.fold ~var:(fun typ _ -> Type.var (decode_variable typ)) ~form:Type.form


  let decode_scheme sch =
    List.map (G.variables sch) ~f:decode_variable, decode (G.root sch)


  (* ----------------------------------------------------------------------- *)

  exception Unify of Type.t * Type.t

  let unify typ1 typ2 =
    try U.unify typ1 typ2 with
    | U.Unify (typ1, typ2) -> raise (Unify (decode typ1, decode typ2))


  (* TODO: Find a representation for \mu types! *)
  exception Cycle of U.Type.t

  (* TODO: Add exception handling for rigid var check! *)
  let exit state ~rigid_vars ~roots =
    try G.exit state ~rigid_vars ~roots with
    | U.Cycle typ -> raise (Cycle typ)


  (* ----------------------------------------------------------------------- *)

  type state =
    { generalization_state : G.state
    ; substitution : (int, U.Type.t) Hashtbl.t
    }

  let make_state () =
    { generalization_state = G.make_state ()
    ; substitution = Hashtbl.create (module Int)
    }


  let find state (var : C.variable) =
    Hashtbl.find_exn state.substitution (var :> int)


  let bind state (var : C.variable) (typ : U.Type.t) =
    Hashtbl.set state.substitution ~key:(var :> int) ~data:typ;
    typ


  let bind_flexible state ((var : C.variable), form_opt) =
    let typ =
      match form_opt with
      | None -> G.fresh_var state.generalization_state Flexible
      | Some form ->
        G.fresh_form
          state.generalization_state
          (Type_former.map form ~f:(find state))
    in
    bind state var typ


  let bind_rigid state (var : C.variable) =
    let typ = G.fresh_var state.generalization_state Rigid in
    bind state var typ


  (* ----------------------------------------------------------------------- *)

  let solve cst =
    (* [decode] is shadowed when opening [Constraint]. *)
    let decode_ = decode in
    let open Constraint in
    (* Initialize generalization state. *)
    let state = make_state () in
    (* Helper function for extending an env w/ several binders *)
    let env_extends_bindings env bindings =
      Env.extends_typs
        env
        (List.map bindings ~f:(fun (x, v) -> x, find state v))
    in
    let rec solve : type a. env:Env.t -> a Constraint.t -> a Elaborate.t =
      let open Elaborate in
      fun ~env cst ->
        match cst with
        | True -> return ()
        | Map (cst, f) ->
          let v = solve ~env cst in
          map v ~f
        | Conj (cst1, cst2) -> both (solve ~env cst1) (solve ~env cst2)
        | Eq (v, w) ->
          unify (find state v) (find state w);
          return ()
        | Def (bindings, in_) ->
          let env = env_extends_bindings env bindings in
          solve ~env in_
        | Match (cst, cases) ->
          let v = solve ~env cst in
          let vs =
            List.map cases ~f:(fun (Case { bindings; in_ }) ->
                let env = env_extends_bindings env bindings in
                solve ~env in_)
          in
          both v (list vs)
        | Exist (bindings, cst) ->
          List.iter ~f:(fun b -> ignore (bind_flexible state b)) bindings;
          solve ~env cst
        | Instance (x, v) ->
          let sch = Env.find env x in
          let instance_variables, w =
            G.instantiate state.generalization_state sch
          in
          unify (find state v) w;
          fun () -> List.map ~f:decode_ instance_variables
        | Let (let_binding, cst) ->
          let let_binding, env = solve_let_binding ~env let_binding in
          let v = solve ~env cst in
          both let_binding v
        | Letn (let_bindings, cst) ->
          let let_bindings, env = solve_let_bindings ~env let_bindings in
          let v = solve ~env cst in
          both let_bindings v
        | Let_rec (let_rec_bindings, cst) ->
          let let_rec_bindings, env =
            solve_let_rec_bindings ~env let_rec_bindings
          in
          let v = solve ~env cst in
          both let_rec_bindings v
        | Forall (vars, cst) ->
          (* Enter a new region *)
          G.enter state.generalization_state;
          (* Introduce the rigid variables *)
          let rigid_vars = List.map ~f:(fun var -> bind_rigid state var) vars in
          (* Solve the constraint *)
          let v = solve ~env cst in
          (* Generalize and exit *)
          ignore (exit state.generalization_state ~rigid_vars ~roots:[]);
          v
        | Decode v -> fun () -> decode_ (find state v)
    and solve_let_rec_bindings
        : type a.
          env:Env.t
          -> a let_rec_binding list
          -> a term_let_rec_binding list Elaborate.t * Env.t
      =
     fun ~env bindings ->
      G.enter state.generalization_state;
      (* Initialize the fresh flexible and rigid variables for each of the bindings *)
      let vars =
        bindings
        |> List.map
             ~f:(fun (Let_rec_binding { flexible_vars; rigid_vars; _ }) ->
               ( List.map ~f:(bind_flexible state) flexible_vars
               , List.map ~f:(bind_rigid state) rigid_vars ))
      in
      let rigid_vars = vars |> List.map ~f:snd |> List.join in
      let vars =
        vars
        |> List.map ~f:(fun (flexible_vars, rigid_vars) ->
               flexible_vars @ rigid_vars)
      in
      let types =
        List.map bindings ~f:(fun (Let_rec_binding { binding = _, v; _ }) ->
            find state v)
      in
      let rec_env =
        env_extends_bindings
          env
          (List.map
             ~f:(fun (Let_rec_binding { binding; _ }) -> binding)
             bindings)
      in
      let values =
        List.map bindings ~f:(fun (Let_rec_binding { in_; _ }) ->
            solve ~env:rec_env in_)
      in
      let generalizable, schemes =
        exit state.generalization_state ~rigid_vars ~roots:types
      in
      let generalizable =
        Hash_set.of_list (module G.Unifier.Type) generalizable
      in
      let env, bindings =
        List.zip_exn bindings schemes
        |> List.fold_left
             ~init:(env, [])
             ~f:(fun (env, bindings) (Let_rec_binding { binding = v, _; _ }, s)
                -> Env.extend env v s, (v, s) :: bindings)
      in
      (* Compute bounds of each solved value *)
      let bound_values =
        List.map2_exn vars values ~f:(fun vars value () ->
            ( List.filter vars ~f:(Hash_set.mem generalizable)
              |> List.map ~f:decode_variable
            , value () ))
      in
      ( List.map2_exn bindings bound_values ~f:(fun (x, s) value () ->
            (x, decode_scheme s), value ())
        |> Elaborate.list
      , env )
    and solve_let_binding
        : type a.
          env:Env.t -> a let_binding -> a term_let_binding Elaborate.t * Env.t
      =
     fun ~env (Let_binding { rigid_vars; flexible_vars; bindings; in_ }) ->
      (* Enter a new region *)
      G.enter state.generalization_state;
      (* Initialize fresh flexible and rigid variables *)
      let _flexible_vars =
        List.map ~f:(fun b -> bind_flexible state b) flexible_vars
      and rigid_vars =
        List.map ~f:(fun var -> bind_rigid state var) rigid_vars
      in
      (* Convert the constraint types into graphic types *)
      let typs = List.map bindings ~f:(fun (_, v) -> find state v) in
      (* Solve the constraint of the let binding *)
      let v1 = solve ~env in_ in
      (* Generalize and exit *)
      let generalizable, schs =
        exit state.generalization_state ~rigid_vars ~roots:typs
      in
      (* Extend environment *)
      let env, bindings =
        List.zip_exn bindings schs
        |> List.fold_left
             ~init:(env, [])
             ~f:(fun (env, bindings) ((var, _), sch) ->
               Env.extend env var sch, (var, sch) :: bindings)
      in
      (* Return binding and extended environment *)
      ( (fun () ->
          ( List.map ~f:(fun (var, sch) -> var, decode_scheme sch) bindings
          , (List.map ~f:decode_variable generalizable, v1 ()) ))
      , env )
    and solve_let_bindings
        : type a.
          env:Env.t
          -> a let_binding list
          -> a term_let_binding list Elaborate.t * Env.t
      =
     fun ~env let_bindings ->
      let let_bindings, env =
        List.fold_right
          let_bindings
          ~f:(fun let_binding (let_bindings, env) ->
            let let_binding, env = solve_let_binding ~env let_binding in
            let_binding :: let_bindings, env)
          ~init:([], env)
      in
      Elaborate.list let_bindings, env
    in
    Elaborate.run (solve ~env:Env.empty cst)
end
