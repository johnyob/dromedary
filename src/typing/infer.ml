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

open Parsing
open Base

(* Instantiate the constraints library using the [Algebra] defined in {algebra.ml}. *)
open Algebra
module Constraints = Constraints.Make (Algebra)
open Constraints

(* [t1 @-> t2] returns the arrow type [t1 -> t2]. *)
let ( @-> ) x y = Type.former (Type_former.Arrow (x, y))

(* [tuple [t1; ...; tn]] returns the tuple type [t1 * ... * tn]. *)
let tuple ts = Type.former (Type_former.Tuple ts)

(* [constr [t1; ..; tn] constr'] returns the type former (or type constructor) [(t1, .., tn) constr']. *)
let constr ts constr = Type.former (Type_former.Constr (ts, constr))

(* [alias t x] returns the alias type [t as x]. *)
let alias t x = Type.mu x t

(* [int, bool] and [unit] are the type formers for the primitive [int, bool, unit] types. *)
let int = Type.former (Type_former.Constr ([], "int"))
let bool = Type.former (Type_former.Constr ([], "bool"))
let unit = Type.former (Type_former.Constr ([], "unit"))

open Ast_types
open Parsetree
(* open Typedtree *)
open Types

(* [convert_core_type var_env core_type] converts core type [core_type] to [Type.t]. *)
let convert_core_type var_env core_type =
  let rec convert_core_type t =
    let open Result.Let_syntax in
    match t with
    | Ptyp_var x ->
      Result.of_option (Map.find var_env x) ~error:(`Unbound_type_variable x) >>| Type.var
    | Ptyp_arrow (t1, t2) ->
      let%bind t1 = convert_core_type t1 in
      let%bind t2 = convert_core_type t2 in
      return (t1 @-> t2)
    | Ptyp_tuple ts ->
      let%bind ts = List.map ts ~f:convert_core_type |> Result.all in
      return (tuple ts)
    | Ptyp_constr (ts, constr') ->
      let%bind ts = List.map ts ~f:convert_core_type |> Result.all in
      return (constr ts constr')
  in
  convert_core_type core_type

(* [convert_type_expr var_env type_expr] converts type expression [type_expr] to [Type.t]. *)
let convert_type_expr var_env t =
  let rec convert_type_expr t =
    let open Result.Let_syntax in
    match t with
    | Ttyp_var x -> Result.of_option (Map.find var_env x) ~error:(`Unbound_type_variable x) >>| Type.var
    | Ttyp_arrow (t1, t2) -> 
      let%bind t1 = convert_type_expr t1 in
      let%bind t2 = convert_type_expr t2 in
      return (t1 @-> t2)
    | Ttyp_tuple ts -> 
      let%bind ts = List.map ts ~f:convert_type_expr |> Result.all in
      return (tuple ts)
    | Ttyp_constr (ts, constr') ->
      let%bind ts = List.map ts ~f:convert_type_expr |> Result.all in
      return (constr ts constr')
    | Ttyp_alias (t, x) -> 
      let%bind t = convert_type_expr t in
      return (alias t x)
  in
  convert_type_expr t

(* [infer_constant const] returns the type of [const]. *)
let infer_constant const =
  match const with
  | Const_int _ -> int
  | Const_bool _ -> bool
  | Const_unit -> unit

(* [infer_primitive prim] returns the type of [prim]. *)
let infer_primitive prim =
  match prim with
  | Prim_add | Prim_sub | Prim_div | Prim_mul -> int @-> int @-> int


module Inference_monad = struct
  module State = struct
    type t = (String.t, Constraint.variable, String.comparator_witness) Map.t
  end

  include Monad.State.Make (State)

end

(* 

(* ------------------------------------------------------------------------- *)

module Infer_monad = struct
  (* Standard reader monad *)

  module State = struct
    type t = (String.t, variable, String.comparator_witness) Map.t
  end

  type 'a t = State.t -> 'a

  module Basic : Monad.Basic with type 'a t = 'a t = struct
    type nonrec 'a t = 'a t

    let bind t ~f state =
      let x = t state in
      f x state


    let return x _ = x
    let map = `Custom (fun t ~f state -> f (t state))
  end

  include Monad.Make (Basic)

  let lift t _ = t
  let run t state = t state
  let read () state = state
  let local t ~f state = t (f state)
end

module Infer_computation = struct
  include Computation.Make (Infer_monad)

  let local t ~f = lift (Infer_monad.local (run t) ~f)

  let extends t ~var_env =
    local t ~f:(fun var_env' ->
        Map.merge_skewed var_env' var_env ~combine:(fun ~key:_ _ var2 -> var2))
end

(* ------------------------------------------------------------------------- *)

let infer_constructor env constr_name constr_type
    : variable list
      * constructor_description Constraint.t
      * Constraint.Type.t option
  =
  (* Determine the constructor argument and type parameters using
     the environment [env] and the constructor name [constr_name]. *)
  let { constructor_arg = constr_arg
      ; constructor_type = constr_type'
      ; constructor_type_params = constr_type_params
      ; _
      }
    =
    Env.find_constr env constr_name
  in
  (* Compute a fresh set of existential variables, which will be 
     bound later. *)
  let constr_type_param_var_alist =
    constr_type_params |> List.map ~f:(fun type_param -> type_param, fresh ())
  in
  (* Compute the inferred type using the existential variables. *)
  let constr_arg, constr_type' =
    let constr_type_params_env =
      Map.of_alist_exn (module String) constr_type_param_var_alist
    in
    ( Option.(constr_arg >>| convert_type_expr constr_type_params_env)
    , convert_type_expr constr_type_params_env constr_type' )
  in
  let constr_desc =
    let open Constraint.Let_syntax in
    let%map () = constr_type =~ constr_type'
    and constr_type = decode constr_type'
    and constr_arg =
      match constr_arg with
      | None -> return None
      | Some constr_arg ->
        let%map constr_arg = decode constr_arg in
        Some constr_arg
    in
    { constructor_name = constr_name
    ; constructor_type = constr_type
    ; constructor_arg = constr_arg
    }
  in
  List.map ~f:snd constr_type_param_var_alist, constr_desc, constr_arg


let infer_label env label label_type
    : variable list * label_description Constraint.t * Constraint.Type.t
  =
  (* Determine the constructor argument and type parameters using
     the environment [env] and the constructor name [constr_name]. *)
  let { label_arg; label_type = label_type'; label_type_params; _ } =
    Env.find_label env label
  in
  (* Compute a fresh set of existential variables, which will be 
    bound later. *)
  let label_type_param_var_alist =
    label_type_params |> List.map ~f:(fun type_param -> type_param, fresh ())
  in
  (* Compute the inferred type using the existential variables. *)
  let label_arg, label_type' =
    let label_type_params_env =
      Map.of_alist_exn (module String) label_type_param_var_alist
    in
    ( convert_type_expr label_type_params_env label_arg
    , convert_type_expr label_type_params_env label_type' )
  in
  let label_desc =
    let open Constraint.Let_syntax in
    let%map () = label_type =~ label_type'
    and label_type = decode label_type'
    and label_arg = decode label_arg in
    { label_name = label; label_type; label_arg }
  in
  List.map ~f:snd label_type_param_var_alist, label_desc, label_arg


let inst_label env label label_arg label_type =
  let vars, label_desc, label_arg' = infer_label env label label_type in
  exists vars (label_arg =~ label_arg' >> label_desc)


(* ------------------------------------------------------------------------- *)

module Fragment = struct
  exception Non_linear_pattern of string

  type t = (String.t, Type.t, String.comparator_witness) Map.t

  let empty = Map.empty (module String)
  let singleton x typ = Map.singleton (module String) x typ

  let extend t x typ =
    try Map.add_exn t ~key:x ~data:typ with
    | _ -> raise (Non_linear_pattern x)


  let merge (t1 : t) (t2 : t) : t =
    Map.merge_skewed t1 t2 ~combine:(fun ~key _ _ ->
        raise (Non_linear_pattern key))


  let to_bindings t : binding list =
    Map.to_alist t |> List.map ~f:(fun (x, t) -> x #= t)
end

(* Idea: We extend computations w/ standard monad transformers
   e.g. Writer computation, Reader computation, etc *)

module Pattern_monad = struct
  type 'a t = (Fragment.t * 'a) Infer_monad.t

  open Infer_monad.Let_syntax

  module Basic : Monad.Basic with type 'a t = 'a t = struct
    type nonrec 'a t = 'a t

    let bind t ~f =
      let%bind fragment1, x = t in
      let%bind fragment2, y = f x in
      return (Fragment.merge fragment1 fragment2, y)


    let return x = return (Fragment.empty, x)
    let map = `Custom (fun t ~f -> t >>| fun (fragment, x) -> fragment, f x)
  end

  let write state = return (state, ())
  let read t = t >>| fun (state, _) -> state, state
  let listen t = t >>| fun (state, x) -> state, (state, x)
  let run t = t
  let lift t = t >>| fun x -> Fragment.empty, x
  let extend x typ = write (Fragment.singleton x typ)
  let read () = lift (Infer_monad.read ())

  include Monad.Make (Basic)
end

module Pattern_computation = Computation.Make (Pattern_monad)

let infer_pat env pat pat_type
    : (Fragment.t * Typedtree.pattern Constraint.t) Infer_monad.t
  =
  let open Pattern_computation in
  let open Let_syntax in
  let rec infer_pat pat pat_type
      : Typedtree.pattern Pattern_computation.Computation.t
    =
    let%sub pat_desc = infer_pat_desc pat pat_type in
    return
      (let%map pat_desc = pat_desc
       and pat_type = decode pat_type in
       { pat_desc; pat_type })
  and infer_pat_desc pat pat_type
      : Typedtree.pattern_desc Pattern_computation.Computation.t
    =
    match pat with
    | Ppat_any -> const Tpat_any
    | Ppat_var x -> const (Tpat_var x)
    | Ppat_alias (pat, x) ->
      let%sub pat = infer_pat pat pat_type in
      let%bind () = Pattern_monad.extend x pat_type in
      return
        (let%map pat = pat in
         Tpat_alias (pat, x))
    | Ppat_constant constant ->
      return
        (let%map () = pat_type =~ infer_constant constant in
         Tpat_constant constant)
    | Ppat_tuple pats ->
      let%bind vars, pats = infer_pats pats in
      return
        (exists
           vars
           (let%map () = pat_type =~ tuple (List.map vars ~f:Type.var)
            and pats = all pats in
            Tpat_tuple pats))
    | Ppat_construct (constr, None) ->
      let constr_type_param_vars, constr_desc, arg_pat_type =
        infer_constructor env constr pat_type
      in
      (match arg_pat_type with
      | Some _ -> assert false
      | None ->
        return
          (exists
             constr_type_param_vars
             (let%map constr_desc = constr_desc in
              Tpat_construct (constr_desc, None))))
    | Ppat_construct (constr, Some arg_pat) ->
      let constr_type_param_vars, constr_desc, arg_pat_type =
        infer_constructor env constr pat_type
      in
      (match arg_pat_type with
      | None -> assert false
      | Some arg_pat_type ->
        let%sub arg_pat = infer_pat arg_pat arg_pat_type in
        return
          (exists
             constr_type_param_vars
             (let%map constr_desc = constr_desc
              and arg_pat = arg_pat in
              Tpat_construct (constr_desc, Some arg_pat))))
    | Ppat_constraint (pat, pat_type') ->
      let%bind var_env = Pattern_monad.read () in
      let pat_type' = convert_core_type var_env pat_type' in
      let%sub pat_desc = infer_pat_desc pat pat_type' in
      return
        (let%map () = pat_type =~ pat_type'
         and pat_desc = pat_desc in
         pat_desc)
  (* Make this into a pattern i.e. State computation *)
  and infer_pats pats
      : (variable list * Typedtree.pattern Constraint.t list) Pattern_monad.t
    =
    let open Pattern_monad.Let_syntax in
    List.fold_left
      pats
      ~init:(return ([], []))
      ~f:(fun accum pat ->
        let var = fresh () in
        let%bind pat = Pattern_computation.run (infer_pat pat (Type.var var))
        and vars, pats = accum in
        return (var :: vars, pat :: pats))
  in
  Pattern_computation.run (infer_pat pat pat_type)


(* ------------------------------------------------------------------------- *)

(* Expressions *)

let infer_exp env exp exp_type =
  let open Infer_computation in
  let open Let_syntax in
  let rec infer_exp exp exp_type
      : Typedtree.expression Infer_computation.Computation.t
    =
    let%sub exp_desc = infer_exp_desc exp exp_type in
    return
      (let%map exp_desc = exp_desc
       and exp_type = decode exp_type in
       { exp_desc; exp_type })
  and infer_exp_desc exp exp_type
      : Typedtree.expression_desc Infer_computation.Computation.t
    =
    match exp with
    | Pexp_var x ->
      return
        (let%map instances = inst x exp_type in
         Texp_var (x, instances))
    | Pexp_prim prim ->
      return
        (let%map () = exp_type =~ infer_primitive prim in
         Texp_prim prim)
    | Pexp_const const ->
      return
        (let%map () = exp_type =~ infer_constant const in
         Texp_const const)
    | Pexp_fun (pat, exp) ->
      let var1, var2 = fresh (), fresh () in
      let tvar1, tvar2 = Type.var var1, Type.var var2 in
      let%bind fragment, pat = infer_pat env pat tvar1 in
      let%sub exp = infer_exp exp tvar2 in
      return
        (exists
           [ var1; var2 ]
           (let%map () = exp_type =~ tvar1 @-> tvar2
            and pat = pat
            and exp = def ~bindings:(Fragment.to_bindings fragment) ~in_:exp in
            Texp_fun (pat, exp)))
    | Pexp_app (exp1, exp2) ->
      let var = fresh () in
      let tvar = Type.var var in
      let%sub exp1 = infer_exp exp1 (tvar @-> exp_type) in
      let%sub exp2 = infer_exp exp2 tvar in
      return
        (exists
           [ var ]
           (let%map exp1 = exp1
            and exp2 = exp2 in
            Texp_app (exp1, exp2)))
    | Pexp_constraint (exp, exp_type') ->
      let%bind var_env = Infer_monad.read () in
      let exp_type' = convert_core_type var_env exp_type' in
      let%sub exp_desc = infer_exp_desc exp exp_type' in
      return
        (let%map () = exp_type =~ exp_type'
         and exp_desc = exp_desc in
         exp_desc)
    | Pexp_construct (constr, None) ->
      let constr_type_param_vars, constr_desc, arg_exp_type =
        infer_constructor env constr exp_type
      in
      (match arg_exp_type with
      | Some _ -> assert false
      | None ->
        return
          (exists
             constr_type_param_vars
             (let%map constr_desc = constr_desc in
              Texp_construct (constr_desc, None))))
    | Pexp_construct (constr, Some arg_exp) ->
      let constr_type_param_vars, constr_desc, arg_exp_type =
        infer_constructor env constr exp_type
      in
      (match arg_exp_type with
      | None -> assert false
      | Some arg_exp_type ->
        let%sub arg_exp = infer_exp arg_exp arg_exp_type in
        return
          (exists
             constr_type_param_vars
             (let%map constr_desc = constr_desc
              and arg_exp = arg_exp in
              Texp_construct (constr_desc, Some arg_exp))))
    | Pexp_tuple exps ->
      let%bind vars, exps = infer_exps exps in
      return
        (exists
           vars
           (let%map () = exp_type =~ tuple (List.map vars ~f:Type.var)
            and exps = all exps in
            Texp_tuple exps))
    | Pexp_match (match_exp, cases) ->
      let var = fresh () in
      let tvar = Type.var var in
      let%sub match_exp = infer_exp match_exp tvar in
      let%sub cases = infer_cases cases tvar exp_type in
      return
        (exists
           [ var ]
           (let%map match_exp = match_exp
            and match_exp_type = decode tvar
            and cases = cases in
            Texp_match (match_exp, match_exp_type, cases)))
    | Pexp_ifthenelse (if_exp, then_exp, else_exp) ->
      let%sub if_exp = infer_exp if_exp bool in
      let%sub then_exp = infer_exp then_exp exp_type in
      let%sub else_exp = infer_exp else_exp exp_type in
      return
        (let%map if_exp = if_exp
         and then_exp = then_exp
         and else_exp = else_exp in
         Texp_ifthenelse (if_exp, then_exp, else_exp))
    | Pexp_exists (vars, exp) ->
      let vars_env_alist = List.map vars ~f:(fun x -> x, fresh ()) in
      let%sub exp =
        extends
          ~var_env:(Map.of_alist_exn (module String) vars_env_alist)
          (infer_exp_desc exp exp_type)
      in
      return (exists (List.map vars_env_alist ~f:snd) exp)
    | Pexp_forall (vars, exp) ->
      let vars_env_alist = List.map vars ~f:(fun x -> x, fresh ()) in
      let var = fresh () in
      let%sub exp_desc =
        extends
          ~var_env:(Map.of_alist_exn (module String) vars_env_alist)
          (infer_exp_desc exp (Type.var var))
      in
      let internal_name = "@dromedary.internal.pexp_forall" in
      return
        (let%map _, (_, exp_desc), _ =
           let_
             ~rigid:(List.map vars_env_alist ~f:snd)
             ~flexible:[ var ]
             ~bindings:(exp_desc, [ internal_name #= (Type.var var) ])
             ~in_:(inst internal_name exp_type)
         in
         exp_desc)
    | Pexp_record label_exps ->
      let%sub label_exps =
        List.map label_exps ~f:(fun (label, exp) ->
            let var2 = fresh () in
            let tvar2 = Type.var var2 in
            let%sub exp = infer_exp exp tvar2 in
            let label_desc = inst_label env label tvar2 exp_type in
            return
              (exists
                 [ var2 ]
                 (let%map exp = exp
                  and label_desc = label_desc in
                  label_desc, exp)))
        |> Infer_computation.Computation.all
      in
      return
        (let%map label_exps = label_exps in
         Texp_record label_exps)
    | Pexp_field (exp, label) ->
      let var = fresh () in
      let tvar = Type.var var in
      let%sub exp = infer_exp exp tvar in
      let label_desc = inst_label env label exp_type tvar in
      return
        (exists
           [ var ]
           (let%map exp = exp
            and label_desc = label_desc in
            Texp_field (exp, label_desc)))
    | _ -> assert false
  and infer_exps exps =
    let open Infer_monad.Let_syntax in
    List.fold_left
      exps
      ~init:(return ([], []))
      ~f:(fun accum exp ->
        let var = fresh () in
        let%map exp = Infer_computation.run (infer_exp exp (Type.var var))
        and vars, exps = accum in
        var :: vars, exp :: exps)
  and infer_cases cases lhs_type rhs_type =
    List.map cases ~f:(fun { pc_lhs; pc_rhs } ->
        let%bind fragment, pat = infer_pat env pc_lhs lhs_type in
        let%sub exp = infer_exp pc_rhs rhs_type in
        return
          (let%map tc_lhs = pat
           and tc_rhs =
             def ~bindings:(Fragment.to_bindings fragment) ~in_:exp
           in
           { tc_lhs; tc_rhs }))
    |> Infer_computation.Computation.all
  in
  Infer_computation.run (infer_exp exp exp_type) *)
