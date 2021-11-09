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

(* This module implements a constraint solver and term elaborator,
   based on F. Pottier's paper ??. *)

open Base
open Intf

(* ------------------------------------------------------------------------- *)

module Make (Term_var : Term_var) (Types : Types) = struct
  (* ----------------------------------------------------------------------- *)

  module Constraint = Constraint.Make (Term_var) (Types)

  (* Aliases *)
  module C = Constraint
  module G = Generalization.Make (Types.Former)
  module U = G.Unifier

  (* ----------------------------------------------------------------------- *)

  module Type_var = Types.Var
  module Type_former = Types.Former
  module Type = Types.Type

  (* ----------------------------------------------------------------------- *)

  (* Applicative structure used for elaboration. *)

  module Elaborate = struct
    type 'a t = unit -> 'a

    let run t = t ()
    let return x () = x
    let map t ~f () = f (t ())
    let both t1 t2 () = t1 (), t2 ()
    let list ts () = List.map ts ~f:run
  end

  (* ----------------------------------------------------------------------- *)

  (* An environment in our constraint solver is defined as a 
     partial finite function from term variables to schemes. 
     
     We implement this using a [Map]. 
     
     We favor [Map] over [Hashtbl] here since we want immutability 
     for recursive calls, as modifications in a local block shouldn't
     affect the overall environment 

     e.g. let x : 'a ... 'b. [ let y : 'c ... 'd. [ C ] in C' ] in C'',
     here binding y shouldn't affect the environment for C''. 
     This would not be the case for a mutable mapping (using side-effecting
     operations). 
     
     Using [Hashtbl] would implement a dynamically scoped environment
     as opposed to a lexically scoped one. *)

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

    (* let extends_schs t bindings = 
      List.fold_left bindings ~init:t ~f:(fun t (var, sch) ->
        extend t var sch) *)

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

  let solve cst =
    let open Constraint in
    (* Initialize generalization state. *)
    let state = G.make_state () in
    (* Constaint variables are encoded using immutable integers. When solving, 
       we need to map these to unification variables. *)
    let cst_var_env = Hashtbl.create (module Int) in
    (* A lookup function for constraint variables. TODO: Error handling *)
    let find_cst_var var = Hashtbl.find_exn cst_var_env var in
    (* A conversion function between constraint types and graphic types. *)
    let rec convert_cst_typ typ =
      match typ with
      | Type.Var var -> find_cst_var var
      | Type.Form form ->
        G.fresh_form state (Type_former.map form ~f:convert_cst_typ)
    in
    (* A binding function for constraint variables *)
    let bind_cst_var cst_var flexibility =
      let typ = G.fresh_var state flexibility in
      Hashtbl.set cst_var_env ~key:cst_var ~data:typ;
      typ
    in
    (* Helper function for extending an env w/ several binders *)
    let env_extends_bindings env bindings =
      Env.extends_typs
        env
        (List.map bindings ~f:(fun (var, typ) -> var, convert_cst_typ typ))
    in
    let rec solve : type a. env:Env.t -> a Constraint.t -> a Elaborate.t =
      let open Elaborate in
      fun ~env cst ->
        match cst with
        | Cst_true -> return ()
        | Cst_false -> assert false
        | Cst_map (cst, f) ->
          let v = solve ~env cst in
          map v ~f
        | Cst_conj (cst1, cst2) -> both (solve ~env cst1) (solve ~env cst2)
        | Cst_eq (t1, t2) ->
          unify (convert_cst_typ t1) (convert_cst_typ t2);
          return ()
        | Cst_def (cdbs, cst) ->
          let env = env_extends_bindings env cdbs in
          solve ~env cst
        | Cst_match (cst, ccases) ->
          let v = solve ~env cst in
          let vs =
            List.map ccases ~f:(fun { ccase_bs; ccase_cst } ->
                let env = env_extends_bindings env ccase_bs in
                solve ~env ccase_cst)
          in
          both v (list vs)
        | Cst_exist (vars, cst) ->
          List.iter vars ~f:(fun var -> ignore (bind_cst_var var Flexible));
          solve ~env cst
        | Cst_instance (x, t) ->
          let sch = Env.find env x in
          let instance_variables, typ = G.instantiate state sch in
          unify (convert_cst_typ t) typ;
          fun () -> List.map ~f:decode instance_variables
        | Cst_let ({ clb_sch; clb_bs }, cst) ->
          (* Enter a new region *)
          G.enter state;
          (* Initialize fresh flexible and rigid variables *)
          let _flexible_vars =
            List.map clb_sch.csch_flexible_vars ~f:(fun var ->
                bind_cst_var var Flexible)
          and rigid_vars =
            List.map clb_sch.csch_rigid_vars ~f:(fun var ->
                bind_cst_var var Rigid)
          in
          (* Convert the constraint types into graphic types *)
          let typs = List.map clb_bs ~f:(fun (_, typ) -> convert_cst_typ typ) in
          (* Solve the constraint of the let binding *)
          let v1 = solve ~env clb_sch.csch_cst in
          (* Generalize and exit *)
          let generalizable, schs = exit state ~rigid_vars ~roots:typs in
          (* Extend environment *)
          let env, bindings =
            List.zip_exn clb_bs schs
            |> List.fold_left
                 ~init:(env, [])
                 ~f:(fun (env, bindings) ((var, _), sch) ->
                   Env.extend env var sch, (var, sch) :: bindings)
          in
          (* Solve the 2nd constraint w/ extended environment *)
          let v2 = solve ~env cst in
          (* Return *)
          fun () ->
            ( List.map ~f:(fun (var, sch) -> var, decode_scheme sch) bindings
            , (List.map ~f:decode_variable generalizable, v1 ())
            , v2 () )
        | Cst_forall (vars, cst) ->
          (* Enter a new region *)
          G.enter state;
          (* Introduce the rigid variables *)
          let rigid_vars =
            List.map vars ~f:(fun var -> bind_cst_var var Rigid)
          in
          (* Solve the constraint *)
          let v = solve ~env cst in
          (* Generalize and exit *)
          ignore (exit state ~rigid_vars ~roots:[]);
          v
    in
    Elaborate.run (solve ~env:Env.empty cst) 
end
