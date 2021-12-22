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

(* TODO: Reduce number of opens (pollutes global namespace) *)

(* Syntax *)
open Ast_types
open Parsetree
open Typedtree

(* Types *)
open Types
open Algebra
open Constraint

(* [t1 @-> t2] returns the arrow type [t1 -> t2]. *)
let ( @-> ) x y = Type_former.Arrow (x, y)
let ( @--> ) x y = Type.former (x @-> y)

(* [tuple [t1; ...; tn]] returns the tuple type [t1 * ... * tn]. *)
let tuple ts = Type_former.Tuple ts
let tuple_ ts = Type.former (tuple ts)

(* [constr [t1; ..; tn] constr'] returns the type former (or type constructor) 
   [(t1, .., tn) constr']. *)
let constr ts constr = Type_former.Constr (ts, constr)
let constr_ ts constr' = Type.former (constr ts constr')

(* [int, bool] and [unit] are the type formers for the primitive [int, bool, unit] 
   types. *)
let int = Type_former.Constr ([], "int")
let int_ = Type.former int
let bool = Type_former.Constr ([], "bool")
let bool_ = Type.former bool
let unit = Type_former.Constr ([], "unit")
let unit_ = Type.former unit

(* [convert_core_type core_type] converts core type [core_type] to [Type.t]. *)
let rec convert_core_type ~substitution core_type : (Type.t, _) Result.t =
  let open Result in
  let open Let_syntax in
  match core_type with
  | Ptyp_var x -> Substitution.find_var substitution x >>| Type.var
  | Ptyp_arrow (t1, t2) ->
    let%bind t1 = convert_core_type ~substitution t1 in
    let%bind t2 = convert_core_type ~substitution t2 in
    return (t1 @--> t2)
  | Ptyp_tuple ts ->
    let%bind ts = List.map ts ~f:(convert_core_type ~substitution) |> all in
    return (tuple_ ts)
  | Ptyp_constr (ts, constr') ->
    let%bind ts = List.map ts ~f:(convert_core_type ~substitution) |> all in
    return (constr_ ts constr')


(* [convert_type_expr type_expr] converts type expression [type_expr] to [Type.t]. *)
let rec convert_type_expr ~substitution type_expr : (Type.t, _) Result.t =
  let open Result in
  let open Let_syntax in
  match type_expr with
  | Ttyp_var x -> Substitution.find_var substitution x >>| Type.var
  | Ttyp_arrow (t1, t2) ->
    let%bind t1 = convert_type_expr ~substitution t1 in
    let%bind t2 = convert_type_expr ~substitution t2 in
    return (t1 @--> t2)
  | Ttyp_tuple ts ->
    let%bind ts = List.map ts ~f:(convert_type_expr ~substitution) |> all in
    return (tuple_ ts)
  | Ttyp_constr (ts, constr') ->
    let%bind ts = List.map ts ~f:(convert_type_expr ~substitution) |> all in
    return (constr_ ts constr')
  | Ttyp_alias _ -> fail (`Type_expr_contains_alias type_expr)


(* [infer_constant const] returns the type of [const]. *)
let infer_constant const : Type.t =
  match const with
  | Const_int _ -> int_
  | Const_bool _ -> bool_
  | Const_unit -> unit_


(* [infer_primitive prim] returns the type of [prim]. *)
let infer_primitive prim : Type.t =
  match prim with
  | Prim_add | Prim_sub | Prim_div | Prim_mul -> int_ @--> int_ @--> int_
  | Prim_eq -> int_ @--> int_ @--> bool_


let make_constr_desc constr_name constr_arg constr_type
    : constructor_description Constraint.t
  =
  let open Constraint.Let_syntax in
  let%map constr_type = decode constr_type
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


let inst_constr_decl ~env name
    : (Constraint.variable list * Type.t option * Type.t, _) Result.t
  =
  let open Result in
  let open Let_syntax in
  (* Determine the constructor argument and type parameters using
     the environment [env] and the constructor name [name]. *)
  let%bind { constructor_arg = constr_arg
           ; constructor_type = constr_type
           ; constructor_type_params = constr_type_params
           ; _
           }
    =
    Env.find_constr env name
  in
  (* Compute a fresh set of existential variables *)
  let%bind substitution =
    Substitution.of_alist
      (List.map ~f:(fun x -> x, fresh ()) constr_type_params)
    |> Result.map_error ~f:(fun (`Duplicate_type_variable var) ->
           `Duplicate_type_parameter_for_constructor (name, var))
  in
  (* Compute the inferred type using the existential variables. *)
  let%bind constr_arg =
    match constr_arg with
    | Some constr_arg ->
      convert_type_expr ~substitution constr_arg >>| Option.some
    | None -> return None
  in
  let%bind constr_type = convert_type_expr ~substitution constr_type in
  return (Substitution.rng substitution, constr_arg, constr_type)


let inst_label_decl ~env label
    : (Constraint.variable list * Type.t * Type.t, _) Result.t
  =
  let open Result.Let_syntax in
  let%bind { label_arg; label_type; label_type_params; _ } =
    Env.find_label env label
  in
  (* Compute a fresh set of existential variables *)
  let%bind substitution =
    Substitution.of_alist (List.map ~f:(fun x -> x, fresh ()) label_type_params)
    |> Result.map_error ~f:(fun (`Duplicate_type_variable var) ->
           `Duplicate_type_parameter_for_label (label, var))
  in
  (* Compute the inferred type using the existential variables. *)
  let%bind label_arg = convert_type_expr ~substitution label_arg in
  let%bind label_type = convert_type_expr ~substitution label_type in
  return (Substitution.rng substitution, label_arg, label_type)


let make_label_desc label_name label_arg label_type
    : label_description Constraint.t
  =
  let open Constraint.Let_syntax in
  let%map label_type = decode label_type
  and label_arg = decode label_arg in
  { label_name; label_type; label_arg }


module Pattern = struct
  module Computation = Computation.Pattern
  open Computation.Binder
  open Computation

  let convert_core_type core_type : Type.t Computation.t =
    let open Computation.Let_syntax in
    let%bind substitution = substitution in
    of_result
      (convert_core_type ~substitution core_type)
      ~message:(fun (`Unbound_type_variable var) ->
        [%message
          "Unbound type variable when converting core type in pattern"
            (var : string)])


  let inst_constr_decl name : (Type.t option * Type.t) Binder.t =
    let open Binder.Let_syntax in
    let& vars, constr_arg, constr_type =
      let%bind.Computation env = env in
      of_result (inst_constr_decl ~env name) ~message:(function
          | `Duplicate_type_parameter_for_constructor (constr, var) ->
            [%message
              "Duplicate type parameter in constructor in environment"
                (var : string)
                (constr : string)]
          | `Type_expr_contains_alias type_expr ->
            [%message
              "Constructor type in environment contains alias"
                (name : string)
                (type_expr : type_expr)]
          | `Unbound_constructor constr ->
            [%message "Constructor is unbound in environment" (constr : string)]
          | `Unbound_type_variable var ->
            [%message
              "Unbound type variable when instantiating constructor (Cannot \
               occur! Good luck)"
                (var : string)])
    in
    let%bind () = exists_vars vars in
    return (constr_arg, constr_type)


  let infer_constr constr_name constr_type
      : (constructor_description Constraint.t * variable option) Binder.t
    =
    let open Binder.Let_syntax in
    (* Instantiate the constructor description. *)
    let%bind constr_arg, constr_type' = inst_constr_decl constr_name in
    (* Convert [const_arg] and [const_type'] to variables *)
    let%bind constr_arg =
      match constr_arg with
      | Some constr_arg ->
        let%bind constr_arg = of_type constr_arg in
        return (Some constr_arg)
      | None -> return None
    in
    let%bind constr_type' = of_type constr_type' in
    (* Build constraint. *)
    let constr_desc =
      constr_type
      =~ constr_type'
      >> make_constr_desc constr_name constr_arg constr_type
    in
    return (constr_desc, constr_arg)


  let infer pat pat_type =
    let rec infer_pat pat pat_type
        : Typedtree.pattern Constraint.t Computation.t
      =
      let open Computation.Let_syntax in
      let%bind pat_desc = infer_pat_desc pat pat_type in
      return
        (let%map pat_desc = pat_desc
         and pat_type = decode pat_type in
         { pat_desc; pat_type })
    and infer_pat_desc pat pat_type
        : Typedtree.pattern_desc Constraint.t Computation.t
      =
      let open Computation.Let_syntax in
      match pat with
      | Ppat_any -> const Tpat_any
      | Ppat_var x ->
        let%bind () = extend x pat_type in
        const (Tpat_var x)
      | Ppat_alias (pat, x) ->
        let%bind pat = infer_pat pat pat_type in
        let%bind () = extend x pat_type in
        return
          (let%map pat = pat in
           Tpat_alias (pat, x))
      | Ppat_const const ->
        return
          (let%map () = pat_type =~- infer_constant const in
           Tpat_const const)
      | Ppat_tuple pats ->
        let@ vars, pats = infer_pats pats in
        return
          (let%map () = pat_type =~= tuple vars
           and pats = pats in
           Tpat_tuple pats)
      | Ppat_constraint (pat, pat_type') ->
        let@ pat_type' =
          let open Binder.Let_syntax in
          let& pat_type' = convert_core_type pat_type' in
          of_type pat_type'
        in
        let%bind pat_desc = infer_pat_desc pat pat_type' in
        return
          (let%map () = pat_type =~ pat_type'
           and pat_desc = pat_desc in
           pat_desc)
      | Ppat_construct (constr, arg_pat) ->
        let@ constr_desc, arg_pat_type = infer_constr constr pat_type in
        let%bind arg_pat =
          match arg_pat, arg_pat_type with
          | Some arg_pat, Some arg_pat_type ->
            let%bind pat = infer_pat arg_pat arg_pat_type in
            return (pat >>| Option.some)
          | None, None -> const None
          | _, _ ->
            fail
              [%message
                "pattern constructor argument mismatch"
                  (pat : Parsetree.pattern)]
        in
        return
          (let%map constr_desc = constr_desc
           and arg_pat = arg_pat in
           Tpat_construct (constr_desc, arg_pat))
    and infer_pats pats
        : (variable list * Typedtree.pattern list Constraint.t) Binder.t
      =
      let open Binder.Let_syntax in
      let%bind vars, pats =
        List.fold_right
          pats
          ~init:(return ([], []))
          ~f:(fun pat accum ->
            let%bind vars, pats = accum in
            let%bind var = exists () in
            let& pat = infer_pat pat var in
            return (var :: vars, pat :: pats))
      in
      return (vars, Constraint.all pats)
    in
    Computation.run (infer_pat pat pat_type)
end

module Expression = struct
  module Fragment = Computation.Fragment
  module Computation = Computation.Expression
  open Computation.Binder
  open Computation

  (* TODO: Move this somewhere? (It's a library function). *)
  let lift f shallow_type =
    let open Computation.Let_syntax in
    let var = fresh () in
    let%bind t = f var in
    return (Constraint.exists [ var, Some shallow_type ] t)


  (* TODO: Move to computation. *)
  let extend_substitution vars ~f ~message =
    let open Computation.Let_syntax in
    let%bind substitution =
      of_result
        (Substitution.of_alist (List.map ~f:(fun x -> x, fresh ()) vars))
        ~message:(fun (`Duplicate_type_variable var) -> message var)
    in
    let vars = Substitution.rng substitution in
    extend_substitution ~substitution (f vars)


  let convert_core_type core_type : Type.t Computation.t =
    let open Computation.Let_syntax in
    let%bind substitution = substitution in
    of_result
      (convert_core_type ~substitution core_type)
      ~message:(fun (`Unbound_type_variable var) ->
        [%message
          "Unbound type variable when converting core type in expression"
            (var : string)])


  let inst_constr_decl name : (Type.t option * Type.t) Binder.t =
    let open Binder.Let_syntax in
    let& vars, constr_arg, constr_type =
      let%bind.Computation env = env in
      (* TODO: Remove code duplication *)
      of_result (inst_constr_decl ~env name) ~message:(function
          | `Duplicate_type_parameter_for_constructor (constr, var) ->
            [%message
              "Duplicate type parameter in constructor in environment"
                (var : string)
                (constr : string)]
          | `Type_expr_contains_alias type_expr ->
            [%message
              "Constructor type in environment contains alias"
                (name : string)
                (type_expr : type_expr)]
          | `Unbound_constructor constr ->
            [%message "Constructor is unbound in environment" (constr : string)]
          | `Unbound_type_variable var ->
            [%message
              "Unbound type variable when instantiating constructor (Cannot \
               occur! Good luck)"
                (var : string)])
    in
    let%bind () = exists_vars vars in
    return (constr_arg, constr_type)


  let inst_label_decl label : (Type.t * Type.t) Binder.t =
    let open Binder.Let_syntax in
    let& vars, label_arg, constr_type =
      let%bind.Computation env = env in
      of_result (inst_label_decl ~env label) ~message:(function
          | `Duplicate_type_parameter_for_label (label, var) ->
            [%message
              "Duplicate type parameter in label in environment"
                (var : string)
                (label : string)]
          | `Type_expr_contains_alias type_expr ->
            [%message
              "Label type in environment contains alias"
                (label : string)
                (type_expr : type_expr)]
          | `Unbound_label label ->
            [%message "Label is unbound in environment" (label : string)]
          | `Unbound_type_variable var ->
            [%message
              "Unbound type variable when instantiating label (Cannot occur! \
               Good luck)"
                (var : string)])
    in
    let%bind () = exists_vars vars in
    return (label_arg, constr_type)


  let infer_constr constr_name constr_type
      : (constructor_description Constraint.t * variable option) Binder.t
    =
    let open Binder.Let_syntax in
    (* Instantiate the constructor description. *)
    let%bind constr_arg, constr_type' = inst_constr_decl constr_name in
    (* Convert [const_arg] and [const_type'] to variables *)
    let%bind constr_arg =
      match constr_arg with
      | Some constr_arg ->
        let%bind var = of_type constr_arg in
        return (Some var)
      | None -> return None
    in
    (* Build constraint. *)
    let constr_desc =
      constr_type
      =~- constr_type'
      >> make_constr_desc constr_name constr_arg constr_type
    in
    return (constr_desc, constr_arg)


  let infer_label label label_type
      : (label_description Constraint.t * variable) Binder.t
    =
    let open Binder.Let_syntax in
    let%bind label_arg, label_type' = inst_label_decl label in
    (* Convert to variables *)
    let%bind label_arg = of_type label_arg in
    let label_desc =
      label_type =~- label_type' >> make_label_desc label label_arg label_type
    in
    return (label_desc, label_arg)


  let inst_label label label_arg label_type
      : label_description Constraint.t Computation.t
    =
    let open Computation.Let_syntax in
    let@ label_desc, label_arg' = infer_label label label_type in
    return (label_arg =~ label_arg' >> label_desc)


  let infer_pat pat pat_type
      : (binding list * Typedtree.pattern Constraint.t) Binder.t
    =
    let open Binder.Let_syntax in
    (* print_endline
      (Sexp.to_string_hum [%message "infer_pat" (pat : Parsetree.pattern)]); *)
    let& fragment, pat = Pattern.infer pat pat_type in
    let existential_bindings, term_bindings = Fragment.to_bindings fragment in
    (* List.iter existential_bindings ~f:(fun (var, binding) ->
        Format.printf "Variable: %d@." (var :> int);
        Format.printf
          "Binding: %s@."
          ([%sexp (binding : Shallow_type.t option)] |> Sexp.to_string_hum));
    List.iter term_bindings ~f:(fun (term_var, var) ->
        Format.printf "Term Variable: %s@." term_var;
        Format.printf "Bound Variable: %d@." (var :> int)); *)
    let%bind () = exists_bindings existential_bindings in
    return (term_bindings, pat)


  let make_exp_desc_forall vars var exp_desc exp_type =
    let open Constraint.Let_syntax in
    let internal_name = "@dromedary.internal.pexp_forall" in
    let%map term_let_bindings, _ =
      let_
        ~bindings:
          [ ((vars, [ var, None ]) @. exp_desc) @=> [ internal_name #= var ] ]
        ~in_:(inst internal_name exp_type)
    in
    match term_let_bindings with
    | [ (_, (_, exp_desc)) ] -> exp_desc
    | _ -> assert false


  let infer_exp exp exp_type : Typedtree.expression Constraint.t Computation.t =
    let rec infer_exp exp exp_type
        : Typedtree.expression Constraint.t Computation.t
      =
      let open Computation.Let_syntax in
      let%bind exp_desc = infer_exp_desc exp exp_type in
      return
        (let%map exp_desc = exp_desc
         and exp_type = decode exp_type in
         { exp_desc; exp_type })
    and infer_exp_desc exp exp_type
        : Typedtree.expression_desc Constraint.t Computation.t
      =
      let open Computation.Let_syntax in
      match exp with
      | Pexp_var x ->
        return
          (let%map instances = inst x exp_type in
           Texp_var (x, instances))
      | Pexp_prim prim ->
        return
          (let%map () = exp_type =~- infer_primitive prim in
           Texp_prim prim)
      | Pexp_const const ->
        return
          (let%map () = exp_type =~- infer_constant const in
           Texp_const const)
      | Pexp_fun (pat, exp) ->
        let@ var1 = exists () in
        let@ var2 = exists () in
        let@ bindings, pat = infer_pat pat var1 in
        let%bind exp = infer_exp exp var2 in
        return
          (let%map () = exp_type =~= var1 @-> var2
           and pat = pat
           and exp = def ~bindings ~in_:exp in
           Texp_fun (pat, exp))
      | Pexp_app (exp1, exp2) ->
        let@ var = exists () in
        let%bind exp1 = lift (infer_exp exp1) (var @-> exp_type) in
        let%bind exp2 = infer_exp exp2 var in
        return
          (let%map exp1 = exp1
           and exp2 = exp2 in
           Texp_app (exp1, exp2))
      | Pexp_constraint (exp, exp_type') ->
        let%bind exp_type' = convert_core_type exp_type' in
        let@ exp_type' = of_type exp_type' in
        let%bind exp_desc = infer_exp_desc exp exp_type' in
        return
          (let%map () = exp_type =~ exp_type'
           and exp_desc = exp_desc in
           exp_desc)
      | Pexp_tuple exps ->
        let@ vars, exps = infer_exps exps in
        return
          (let%map () = exp_type =~= tuple vars
           and exps = exps in
           Texp_tuple exps)
      | Pexp_match (match_exp, cases) ->
        let@ var = exists () in
        let%bind match_exp = infer_exp match_exp var in
        let%bind cases = infer_cases cases var exp_type in
        return
          (let%map match_exp = match_exp
           and match_exp_type = decode var
           and cases = cases in
           Texp_match (match_exp, match_exp_type, cases))
      | Pexp_ifthenelse (if_exp, then_exp, else_exp) ->
        let%bind if_exp = lift (infer_exp if_exp) bool in
        let%bind then_exp = infer_exp then_exp exp_type in
        let%bind else_exp = infer_exp else_exp exp_type in
        return
          (let%map if_exp = if_exp
           and then_exp = then_exp
           and else_exp = else_exp in
           Texp_ifthenelse (if_exp, then_exp, else_exp))
      | Pexp_exists (vars, exp) ->
        extend_substitution
          vars
          ~f:(fun vars ->
            let@ () = exists_vars vars in
            infer_exp_desc exp exp_type)
          ~message:(fun var ->
            [%message
              "Duplicate variable in existential quantifier (exists)"
                (exp : Parsetree.expression)
                (var : string)])
      | Pexp_forall (vars, exp) ->
        extend_substitution
          vars
          ~f:(fun vars ->
            let var = fresh () in
            let%bind exp_desc = infer_exp_desc exp var in
            return (make_exp_desc_forall vars var exp_desc exp_type))
          ~message:(fun var ->
            [%message
              "Duplicate variable in universal quantifier (forall)"
                (exp : Parsetree.expression)
                (var : string)])
      | Pexp_field (exp, label) ->
        let@ var = exists () in
        let%bind exp = infer_exp exp var in
        let%bind label_desc = inst_label label exp_type var in
        return
          (let%map exp = exp
           and label_desc = label_desc in
           Texp_field (exp, label_desc))
      | Pexp_record label_exps ->
        let%bind label_exps = infer_label_exps label_exps exp_type in
        return
          (let%map label_exps = label_exps in
           Texp_record label_exps)
      | Pexp_construct (constr, arg_exp) ->
        let@ constr_desc, arg_exp_type = infer_constr constr exp_type in
        let%bind arg_exp =
          match arg_exp, arg_exp_type with
          | Some arg_exp, Some arg_exp_type ->
            let%bind exp = infer_exp arg_exp arg_exp_type in
            return (exp >>| Option.some)
          | None, None -> const None
          | _, _ ->
            fail
              [%message
                "expression constructor argument mismatch"
                  (exp : Parsetree.expression)]
        in
        return
          (let%map constr_desc = constr_desc
           and arg_exp = arg_exp in
           Texp_construct (constr_desc, arg_exp))
      | Pexp_let (value_bindings, exp) ->
        (* TODO: Coercion! *)
        let%bind let_bindings = infer_value_bindings value_bindings in
        let%bind exp = infer_exp exp exp_type in
        let to_value_binding (_, (variables, (pat, exp))) =
          { tvb_pat = pat; tvb_expr = variables, exp }
        in
        return
          (let%map let_bindings, exp = let_ ~bindings:let_bindings ~in_:exp in
           Texp_let (List.map ~f:to_value_binding let_bindings, exp))
      | Pexp_let_rec (rec_value_bindings, exp) ->
        let%bind let_bindings = infer_rec_value_bindings rec_value_bindings in
        let%bind exp = infer_exp exp exp_type in
        let to_rec_value_binding ((var, (variables, _)), (_, exp)) =
          { trvb_var = var; trvb_expr = variables, exp }
        in
        return
          (let%map let_bindings, exp =
             let_rec ~bindings:let_bindings ~in_:exp
           in
           Texp_let_rec (List.map ~f:to_rec_value_binding let_bindings, exp))
    and infer_exps exps
        : (variable list * Typedtree.expression list Constraint.t) Binder.t
      =
      let open Binder.Let_syntax in
      let%bind vars, exps =
        List.fold_right
          exps
          ~init:(return ([], []))
          ~f:(fun exp acc ->
            let%bind var = exists () in
            let& exp = infer_exp exp var in
            let%bind vars, exps = acc in
            return (var :: vars, exp :: exps))
      in
      return (vars, Constraint.all exps)
    and infer_cases cases lhs_type rhs_type
        : Typedtree.case list Constraint.t Computation.t
      =
      let open Computation.Let_syntax in
      let%bind cases =
        List.map cases ~f:(fun { pc_lhs; pc_rhs } ->
            let@ bindings, pat = infer_pat pc_lhs lhs_type in
            let%bind exp = infer_exp pc_rhs rhs_type in
            return
              (let%map tc_lhs = pat
               and tc_rhs = def ~bindings ~in_:exp in
               { tc_lhs; tc_rhs }))
        |> all
      in
      return (Constraint.all cases)
    and infer_label_exps label_exps exp_type
        : (label_description * Typedtree.expression) list Constraint.t
        Computation.t
      =
      let open Computation.Let_syntax in
      let%bind label_exps =
        List.map label_exps ~f:(fun (label, exp) ->
            let@ var = exists () in
            let%bind exp = infer_exp exp var in
            let%bind label_desc = inst_label label var exp_type in
            return (label_desc &~ exp))
        |> all
      in
      return (Constraint.all label_exps)
    and infer_value_bindings value_bindings
        : (Typedtree.pattern * Typedtree.expression) let_binding list
        Computation.t
      =
      value_bindings |> List.map ~f:infer_value_binding |> all
    and infer_rec_value_bindings rec_value_bindings
        : Typedtree.expression let_rec_binding list Computation.t
      =
      rec_value_bindings |> List.map ~f:infer_rec_value_binding |> all
    and infer_value_binding { pvb_pat = pat; pvb_expr = exp }
        : (Typedtree.pattern * Typedtree.expression) let_binding Computation.t
      =
      let open Computation.Let_syntax in
      let var = fresh () in
      let%bind fragment, pat = Pattern.infer pat var in
      let existential_bindings, term_bindings = Fragment.to_bindings fragment in
      let%bind exp = infer_exp exp var in
      return
        ((([], (var, None) :: existential_bindings) @. (pat &~ exp))
        @=> term_bindings)
    and infer_rec_value_binding { prvb_var = term_var; prvb_expr = exp }
        : Typedtree.expression let_rec_binding Computation.t
      =
      let open Computation.Let_syntax in
      let var = fresh () in
      let%bind exp = infer_exp exp var in
      return ((([], [ var, None ]) @. exp) @~> (term_var #= var))
    in
    infer_exp exp exp_type


  let infer exp : Typedtree.expression Constraint.t Computation.t =
    let open Computation.Let_syntax in
    let@ var = exists () in
    infer_exp exp var
end

let let_0 ~in_ =
  let_ ~bindings:[ (([], []) @. in_) @=> [] ] ~in_:(return ())
  >>| function
  | [ ([], (vars, t)) ], _ -> vars, t
  | _ -> assert false


let infer exp ~env:env' =
  let open Result.Let_syntax in
  let%bind exp =
    let exp = Expression.infer exp in
    Computation.Expression.(run ~env:env' (exp >>| fun in_ -> let_0 ~in_))
  in
  solve exp
  |> Result.map_error ~f:(function
         | `Unify (type_expr1, type_expr2) ->
           [%message
             "Cannot unify types"
               (type_expr1 : type_expr)
               (type_expr2 : type_expr)]
         | `Cycle type_expr -> [%message "Cycle occurs" (type_expr : type_expr)]
         | `Unbound_term_variable term_var ->
           [%message
             "Term variable is unbound when solving constraint"
               (term_var : string)]
         | `Unbound_constraint_variable var ->
           [%message
             "Constraint variable is unbound when solving constraint"
               ((var :> int) : int)]
         | `Rigid_variable_escape var ->
           [%message
             "Rigid type variable escaped when generalizing" (var : string)])
