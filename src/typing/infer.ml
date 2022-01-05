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

(* {1 : Type combinators} *)

(* [t1 @-> t2] returns the arrow type [t1 -> t2]. *)
let ( @-> ) x y = Type.former (Type_former.Arrow (x, y))

(* [tuple [t1; ...; tn]] returns the tuple type [t1 * ... * tn]. *)
let tuple ts = Type.former (Type_former.Tuple ts)

(* [constr [t1; ..; tn] constr'] returns the type former (or type constructor) 
   [(t1, .., tn) constr']. *)
let constr ts constr' = Type.former (Type_former.Constr (ts, constr'))

(* [int, bool] and [unit] are the type formers for the primitive [int, bool, unit] 
   types. *)
let int = Type.former (Type_former.Constr ([], "int"))
let bool = Type.former (Type_former.Constr ([], "bool"))
let unit = Type.former (Type_former.Constr ([], "unit"))

(* {2 : Shared inference functions} *)

(* [substitution_of_vars vars] returns a substitution w/ 
   domain [vars] bound to fresh variables. *)
let substitution_of_vars ~flexibility vars =
  Substitution.of_alist (List.map ~f:(fun x -> x, (fresh (), flexibility)) vars)


(* [convert_core_type core_type] converts core type [core_type] to [Type.t]. *)
let rec convert_core_type ~substitution core_type : (Type.t, _) Result.t =
  let open Result in
  let open Let_syntax in
  match core_type with
  | Ptyp_var x -> Substitution.find_var substitution x >>| Type.var
  | Ptyp_arrow (t1, t2) ->
    let%bind t1 = convert_core_type ~substitution t1 in
    let%bind t2 = convert_core_type ~substitution t2 in
    return (t1 @-> t2)
  | Ptyp_tuple ts ->
    let%bind ts = List.map ts ~f:(convert_core_type ~substitution) |> all in
    return (tuple ts)
  | Ptyp_constr (ts, constr') ->
    let%bind ts = List.map ts ~f:(convert_core_type ~substitution) |> all in
    return (constr ts constr')


(* [convert_type_expr type_expr] converts type expression [type_expr] to [Type.t]. *)
let rec convert_type_expr ~substitution type_expr : (Type.t, _) Result.t =
  let open Result in
  let open Let_syntax in
  match type_expr with
  | Ttyp_var x -> Substitution.find_var substitution x >>| Type.var
  | Ttyp_arrow (t1, t2) ->
    let%bind t1 = convert_type_expr ~substitution t1 in
    let%bind t2 = convert_type_expr ~substitution t2 in
    return (t1 @-> t2)
  | Ttyp_tuple ts ->
    let%bind ts = List.map ts ~f:(convert_type_expr ~substitution) |> all in
    return (tuple ts)
  | Ttyp_constr (ts, constr') ->
    let%bind ts = List.map ts ~f:(convert_type_expr ~substitution) |> all in
    return (constr ts constr')
  | Ttyp_alias _ -> fail (`Type_expr_contains_alias type_expr)


(* [inst_constr_decl ~env constr] instantiates a constructor declaration w/ constructor name [constr] *)
let inst_constr_decl ~env ~flexibility name
    : ( variable list
        * (variable list * Type.t) option
        * Type.t
        * unit Constraint.t
    , _ ) Result.t
  =
  let open Result in
  let open Let_syntax in
  (* Determine the constructor argument, type and alphas using
     the environment [env] and the constructor name [name]. *)
  let%bind { constructor_arg = constr_arg
           ; constructor_type = constr_type
           ; constructor_alphas = constr_alphas
           ; constructor_constraints = constr_constraints
           ; _
           }
    =
    Env.find_constr env name
  in
  (* Redefined due to repeated error function *)
  let substitution_of_vars vars =
    substitution_of_vars ~flexibility vars
    |> Result.map_error ~f:(fun (`Duplicate_type_variable var) ->
           `Duplicate_type_parameter_for_constructor (name, var))
  in
  (* Compute fresh set of variables for [constr_alphas]. *)
  let%bind substitution = substitution_of_vars constr_alphas in
  let alphas = Substitution.rng substitution in
  (* Compute the constructor (return) type. *)
  let%bind constr_type = convert_type_expr ~substitution constr_type in
  (* Compute the constructor argument. *)
  let%bind constr_arg, substitution =
    match constr_arg with
    | Some
        { constructor_arg_betas = constr_betas
        ; constructor_arg_type = constr_arg
        } ->
      (* Assert that constr_betas and constr_alphas have no intersection. *)
      let%bind () =
        match
          List.find ~f:(List.mem ~equal:String.equal constr_betas) constr_alphas
        with
        | Some var ->
          fail (`Duplicate_type_parameter_for_constructor (name, var))
        | None -> return ()
      in
      (* Compute fresh set of variables for [constr_betas]. *)
      let%bind substitution' = substitution_of_vars constr_betas in
      let betas = Substitution.rng substitution' in
      (* Compute the type for the [constr_arg]. *)
      let substitution = Substitution.merge substitution substitution' in
      let%bind constr_arg = convert_type_expr ~substitution constr_arg in
      (* Return the constructor argument and modified substitution, used for constraints. *)
      return (Some (betas, constr_arg), substitution)
    | None -> return (None, substitution)
  in
  (* Compute the converted type constraints. *)
  let%bind constr_constraints =
    List.map constr_constraints ~f:(fun (type1, type2) ->
        let%bind type1 = convert_type_expr ~substitution type1 in
        let%bind type2 = convert_type_expr ~substitution type2 in
        return (type1 =~ type2))
    |> all
  in
  return
    (alphas, constr_arg, constr_type, Constraint.all_unit constr_constraints)


(* [make_constr_desc constr_name constr_arg constr_type] returns a constraint
   that computes a constructor descriptor. *)
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


(* [inst_label_decl ~env label] instantiates the label w/ label name [label] *)
let inst_label_decl ~env ~flexibility label
    : (variable list * Type.t * Type.t, _) Result.t
  =
  let open Result.Let_syntax in
  let%bind { label_arg; label_type; label_type_params; _ } =
    Env.find_label env label
  in
  (* Compute a fresh set of existential variables *)
  let%bind substitution =
    substitution_of_vars ~flexibility label_type_params
    |> Result.map_error ~f:(fun (`Duplicate_type_variable var) ->
           `Duplicate_type_parameter_for_label (label, var))
  in
  (* Compute the inferred type using the existential variables. *)
  let%bind label_arg = convert_type_expr ~substitution label_arg in
  let%bind label_type = convert_type_expr ~substitution label_type in
  return (Substitution.rng substitution, label_arg, label_type)


(* [make_label_desc label_name label_arg label_type] returns a constraint that computes
   a label descriptor. *)
let make_label_desc label_name label_arg label_type
    : label_description Constraint.t
  =
  let open Constraint.Let_syntax in
  let%map label_type = decode label_type
  and label_arg = decode label_arg in
  { label_name; label_type; label_arg }


(* {4 : GADT functions} *)

(* [is_constr_generalized ~enc constr] returns whether the constructor [constr] is a constructor of a GADT *)
let is_constr_generalized ~env constr : (bool, _) Result.t =
  let open Result.Let_syntax in
  let%map { constructor_constraints; _ } = Env.find_constr env constr in
  not (List.is_empty constructor_constraints)


(* [is_pat_generalized ~env pat] returns whether the pattern [pat] contains a generalized constructor *)
let rec is_pat_generalized ~env pat : (bool, _) Result.t =
  let open Result.Let_syntax in
  match pat with
  | Ppat_construct (constr, pat) ->
    if%bind is_constr_generalized ~env constr
    then return true
    else (
      match pat with
      | Some pat -> is_pat_generalized ~env pat
      | None -> return false)
  | Ppat_tuple pats ->
    let%map is_pats_generalized =
      List.map pats ~f:(is_pat_generalized ~env) |> Result.all
    in
    List.exists ~f:Fn.id is_pats_generalized
  | Ppat_constraint (pat, _) | Ppat_alias (pat, _) ->
    is_pat_generalized ~env pat
  | Ppat_const _ | Ppat_any | Ppat_var _ -> return false


(* [is_case_generalized ~env case] returns whether the case pattern contains a generalized pattern. *)
let is_case_generalized ~env case : (bool, _) Result.t =
  is_pat_generalized ~env case.pc_lhs


(* [is_case_generalized ~env cases] returns whether the cases contains a generalized case. *)
let is_cases_generalized ~env cases : (bool, _) Result.t =
  let open Result.Let_syntax in
  let%map is_cases_generalized =
    List.map cases ~f:(is_case_generalized ~env) |> Result.all
  in
  List.exists ~f:Fn.id is_cases_generalized


let free_variables_of_core_type t : string list =
  let rec loop t =
    match t with
    | Ptyp_var x -> String.Set.singleton x
    | Ptyp_arrow (t1, t2) -> String.Set.union (loop t1) (loop t2)
    | Ptyp_tuple ts | Ptyp_constr (ts, _) ->
      String.Set.union_list (List.map ~f:loop ts)
  in
  loop t |> String.Set.to_list


let is_rigid_annotation ~substitution core_type : (bool, _) Result.t =
  let open Result.Let_syntax in
  let free_variables = free_variables_of_core_type core_type in
  List.map free_variables ~f:(fun x ->
      match%bind Substitution.flexibility_of substitution x with
      | Rigid -> return true
      | Flexible -> return false)
  |> Result.all
  >>| List.for_all ~f:Fn.id


(* {3 : Polymorphic recursion functions} *)

let rec find_annotation exp =
  let open Option.Let_syntax in
  match exp with
  | Pexp_constraint (exp, type_) -> return (exp, type_)
  | Pexp_fun (Ppat_constraint (pat, type1), exp) ->
    let%bind exp, type2 = find_annotation exp in
    return (Pexp_fun (pat, exp), Ptyp_arrow (type1, type2))
  | _ -> None


let rec annotation_of_value_binding
    ({ pvb_pat = pat; pvb_expr = exp; _ } as value_binding)
  =
  let open Option.Let_syntax in
  match pat with
  | Ppat_constraint (pat, type_) ->
    annotation_of_value_binding
      { value_binding with
        pvb_pat = pat
      ; pvb_expr = Pexp_constraint (value_binding.pvb_expr, type_)
      }
  | _ ->
    let%map exp, core_type = find_annotation exp in
    { value_binding with pvb_expr = exp }, core_type


let annotation_of_rec_value_binding value_binding
    : ( [ `Annotated of string list * string * Parsetree.expression * core_type
        | `Unannotated of string list * string * Parsetree.expression
        ]
    , _ ) Result.t
  =
  let open Result in
  let open Let_syntax in
  match annotation_of_value_binding value_binding with
  | Some ({ pvb_vars = vars; pvb_pat = pat; pvb_expr = exp }, type_) ->
    (match pat with
    | Ppat_var term_var -> return (`Annotated (vars, term_var, exp, type_))
    | _ -> fail `Invalid_recursive_binding)
  | None ->
    (match value_binding.pvb_pat with
    | Ppat_var term_var ->
      return
        (`Unannotated
          (value_binding.pvb_vars, term_var, value_binding.pvb_expr))
    | _ -> fail `Invalid_recursive_binding)


(* {4 : Inference} *)

(* [infer_constant const] returns the type of [const]. *)
let infer_constant const : Type.t =
  match const with
  | Const_int _ -> int
  | Const_bool _ -> bool
  | Const_unit -> unit


(* [infer_primitive prim] returns the type of [prim]. *)
let infer_primitive prim : Type.t =
  match prim with
  | Prim_add | Prim_sub | Prim_div | Prim_mul -> int @-> int @-> int
  | Prim_eq -> int @-> int @-> bool


module Pattern = struct
  module Non_generalized = struct
    module Fragment = Computation.Fragment.Non_generalized
    module Computation = Computation.Pattern.Non_generalized
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
      let& constr_alphas, constr_arg, constr_type, _ =
        let%bind.Computation env = env in
        of_result
          (inst_constr_decl ~env ~flexibility:Flexible name)
          ~message:(function
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
              [%message
                "Constructor is unbound in environment" (constr : string)]
            | `Unbound_type_variable var ->
              [%message
                "Unbound type variable when instantiating constructor (Cannot \
                 occur! Good luck)"
                  (var : string)])
      in
      let constr_arg = Option.(constr_arg >>| snd) in
      let%bind () = exists_vars constr_alphas in
      return (constr_arg, constr_type)


    let infer_constr constr_name constr_type
        : (constructor_description Constraint.t * Type.t option) Binder.t
      =
      let open Binder.Let_syntax in
      (* Instantiate the constructor description. *)
      let%bind constr_arg, constr_type' = inst_constr_decl constr_name in
      (* Build constraint. *)
      let constr_desc =
        constr_type
        =~ constr_type'
        >> make_constr_desc constr_name constr_arg constr_type
      in
      return (constr_desc, constr_arg)


    let infer_pat pat pat_type =
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
            (let%map () = pat_type =~ infer_constant const in
             Tpat_const const)
        | Ppat_tuple pats ->
          let@ vars, pats = infer_pats pats in
          return
            (let%map () = pat_type =~ tuple (List.map ~f:Type.var vars)
             and pats = pats in
             Tpat_tuple pats)
        | Ppat_constraint (pat, pat_type') ->
          let%bind pat_type' = convert_core_type pat_type' in
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
              let& pat = infer_pat pat (Type.var var) in
              return (var :: vars, pat :: pats))
        in
        return (vars, Constraint.all pats)
      in
      Computation.run (infer_pat pat pat_type)
  end

  module Generalized = struct
    module Expression_computation = Computation.Expression
    module Fragment = Computation.Fragment.Generalized
    module Computation = Computation.Pattern.Generalized

    let infer_fragment pat pat_type =
      let module Fragment_computation = Computation.Fragment in
      let open Fragment_computation in
      let open Let_syntax in
      let convert_core_type core_type : Type.t Fragment_computation.t =
        let%bind substitution = substitution in
        of_result
          (convert_core_type ~substitution core_type)
          ~on_error:(fun (`Unbound_type_variable var) ->
            [%message
              "Unbound type variable when converting core type in pattern"
                (var : string)])
      in
      let inst_constr_decl name constr_type
          : Type.t option Fragment_computation.t
        =
        let%bind env = env in
        let%bind constr_alphas, constr_arg, constr_type', constr_constraints =
          of_result
            (inst_constr_decl ~env ~flexibility:Rigid name)
            ~on_error:(function
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
                [%message
                  "Constructor is unbound in environment" (constr : string)]
              | `Unbound_type_variable var ->
                [%message
                  "Unbound type variable when instantiating constructor \
                   (Cannot occur! Good luck)"
                    (var : string)])
        in
        let%bind () = exists_vars constr_alphas in
        let%bind () =
          assert_ (constr_type =~ constr_type' >> constr_constraints)
        in
        match constr_arg with
        | Some (constr_betas, constr_arg) ->
          let%bind () = forall_vars constr_betas in
          return (Some constr_arg)
        | None -> return None
      in
      let rec infer_fragment pat pat_type : unit Fragment_computation.t =
        match pat with
        | Ppat_any -> return ()
        | Ppat_var x -> extend x pat_type
        | Ppat_alias (pat, x) ->
          let%bind () = infer_fragment pat pat_type in
          extend x pat_type
        | Ppat_const const -> assert_ (pat_type =~ infer_constant const)
        | Ppat_tuple pats ->
          let%bind vars = infer_fragment_pats pats in
          assert_ (pat_type =~ tuple vars)
        | Ppat_constraint (pat, pat_type') ->
          let%bind pat_type' = convert_core_type pat_type' in
          let%bind () = infer_fragment pat pat_type' in
          assert_ (pat_type =~ pat_type')
        | Ppat_construct (constr, arg_pat) ->
          let%bind arg_pat_type = inst_constr_decl constr pat_type in
          (match arg_pat, arg_pat_type with
          | Some arg_pat, Some arg_pat_type ->
            infer_fragment arg_pat arg_pat_type
          | None, None -> return ()
          | _, _ ->
            fail
              [%message
                "Pattern constructor argument mismatch"
                  (pat : Parsetree.pattern)])
      and infer_fragment_pats pats : Type.t list Fragment_computation.t =
        List.fold_right pats ~init:(return []) ~f:(fun pat accum ->
            let%bind vars = accum in
            let%bind var = exists () in
            let var = Type.var var in
            let%bind () = infer_fragment pat var in
            return (var :: vars))
      in
      let open Expression_computation.Let_syntax in
      let%bind fragment, () =
        Fragment_computation.run (infer_fragment pat pat_type)
      in
      return fragment


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


    let is_constr_generalized constr_name : bool Computation.t =
      let open Computation.Let_syntax in
      let%bind env = env in
      of_result
        (is_constr_generalized ~env constr_name)
        ~message:(fun (`Unbound_constructor constr) ->
          [%message "Constructor is unbound in environment" (constr : string)])


    let inst_constr_decl name
        : (variable list
          * (variable list * Type.t) option
          * Type.t
          * unit Constraint.t)
        Computation.t
      =
      let open Computation.Let_syntax in
      let%bind env = env in
      let%bind constr_alphas, constr_arg, constr_type, constr_constraints =
        of_result
          (inst_constr_decl ~flexibility:Rigid ~env name)
          ~message:(function
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
              [%message
                "Constructor is unbound in environment" (constr : string)]
            | `Unbound_type_variable var ->
              [%message
                "Unbound type variable when instantiating constructor (Cannot \
                 occur! Good luck)"
                  (var : string)])
      in
      return (constr_alphas, constr_arg, constr_type, constr_constraints)


    let infer_constr constr_name constr_type
        : constructor_description Constraint.t Computation.t
      =
      let open Computation.Let_syntax in
      (* Instantiate the constructor description. *)
      let%bind constr_alphas, constr_arg, constr_type', constr_constraint =
        inst_constr_decl constr_name
      in
      (* Bind alphas. *)
      let@ () = exists_vars constr_alphas in
      (* Bind betas if possible. *)
      let@ constr_arg =
        let open Binder.Let_syntax in
        match constr_arg with
        | Some (constr_betas, constr_arg) ->
          let%bind () = exists_vars constr_betas in
          return (Some constr_arg)
        | None -> return None
      in
      (* Build constraint. *)
      let constr_desc =
        constr_type
        =~ constr_type'
        >> constr_constraint
        >> make_constr_desc constr_name constr_arg constr_type
      in
      return constr_desc


    let infer_pat pat gammas pat_type =
      let rec infer_pat pat gammas constraint_ pat_type
          : Typedtree.pattern Constraint.t Computation.t
        =
        let open Computation.Let_syntax in
        let%bind pat_desc = infer_pat_desc pat gammas constraint_ pat_type in
        return
          (let%map pat_desc = pat_desc
           and pat_type = decode pat_type in
           { pat_desc; pat_type })
      and infer_pat_desc pat gammas constraint_ pat_type
          : Typedtree.pattern_desc Constraint.t Computation.t
        =
        let open Computation.Let_syntax in
        match pat with
        | Ppat_any -> const Tpat_any
        | Ppat_var x -> const (Tpat_var x)
        | Ppat_alias (pat, x) ->
          let%bind pat = infer_pat pat gammas constraint_ pat_type in
          return
            (let%map pat = pat in
             Tpat_alias (pat, x))
        | Ppat_const const ->
          return
            (let%map () = pat_type =~ infer_constant const in
             Tpat_const const)
        | Ppat_tuple pats ->
          let%bind vars, pats =
            infer_tuple_pats pats gammas constraint_ pat_type
          in
          return
            (let%map _, _, () =
               gammas
               #. constraint_
               #=> (pat_type =~ tuple (List.map ~f:Type.var vars))
             and pats = pats in
             Tpat_tuple pats)
        | Ppat_constraint (pat, pat_type') ->
          let%bind pat_type' = convert_core_type pat_type' in
          let%bind pat_desc = infer_pat_desc pat gammas constraint_ pat_type' in
          return
            (let%map () = pat_type =~ pat_type'
             and pat_desc = pat_desc in
             pat_desc)
        | Ppat_construct (constr, arg_pat) ->
          (* Instantiate the constructor description. *)
          let%bind alphas, constr_arg, constr_type', constr_constraint =
            inst_constr_decl constr
          in
          let constraint_' = pat_type =~ constr_type' >> constr_constraint in
          (match arg_pat, constr_arg with
          | Some arg_pat, Some (betas, arg_pat_type) ->
            (* Build constraint for constructor descriptor *)
            let constr_desc =
              Constraint.exists
                (alphas @ betas)
                (constraint_'
                >> make_constr_desc constr (Some arg_pat_type) pat_type)
            in
            (* Infer pattern argument *)
            let%bind arg_pat =
              infer_pat
                arg_pat
                (alphas @ betas @ gammas)
                (constraint_ >> constraint_')
                arg_pat_type
            in
            return
              (let%map _, _, constr_desc = gammas #. constraint_ #=> constr_desc
               and arg_pat = arg_pat in
               Tpat_construct (constr_desc, Some arg_pat))
          | None, None ->
            (* Build constraint for constructor descriptor *)
            let constr_desc =
              Constraint.exists
                alphas
                (constraint_' >> make_constr_desc constr None pat_type)
            in
            return
              (let%map _, _, constr_desc =
                 gammas #. constraint_ #=> constr_desc
               in
               Tpat_construct (constr_desc, None))
          | _, _ ->
            fail
              [%message
                "Pattern constructor argument mismatch"
                  (pat : Parsetree.pattern)])
      and infer_tuple_pats pats gammas constraint_ pat_type
          : (variable list * Typedtree.pattern list Constraint.t) Computation.t
        =
        let open Computation.Let_syntax in
        (* Generate fresh variables for the tuple arguments *)
        let vars = List.map ~f:(fun _ -> fresh ()) pats in
        (* Modify [gammas] and [constraint_] according to local inference *)
        let gammas = gammas @ vars
        and constraint_ =
          constraint_ >> (tuple (List.map ~f:Type.var vars) =~ pat_type)
        in
        (* Infer patterns *)
        let%bind pats =
          List.map2_exn vars pats ~f:(fun var pat ->
              infer_pat pat gammas constraint_ (Type.var var))
          |> Computation.all
        in
        return (vars, Constraint.all pats)
      in
      Computation.run (infer_pat pat gammas (Constraint.return ()) pat_type)
  end
end

module Expression = struct
  module Fragment = Computation.Fragment
  module Computation = Computation.Expression
  open Computation.Binder
  open Computation

  (* TODO: Move to computation. *)
  let extend_substitution vars ~flexibility ~f ~message =
    let open Computation.Let_syntax in
    let%bind substitution =
      of_result
        (Substitution.of_alist
           (List.map ~f:(fun x -> x, (fresh (), flexibility)) vars))
        ~message:(fun (`Duplicate_type_variable var) -> message var)
    in
    let vars = Substitution.rng substitution in
    extend_substitution ~substitution (f vars)


  let is_rigid_annotation core_type : bool Computation.t =
    let open Computation.Let_syntax in
    let%bind substitution = substitution in
    of_result (is_rigid_annotation ~substitution core_type) ~message:(fun _ ->
        assert false)


  let convert_core_type core_type : Type.t Computation.t =
    let open Computation.Let_syntax in
    let%bind substitution = substitution in
    of_result
      (convert_core_type ~substitution core_type)
      ~message:(fun (`Unbound_type_variable var) ->
        [%message
          "Unbound type variable when converting core type in expression"
            (var : string)])


  let convert_type_expr ~substitution type_expr : Type.t Computation.t =
    of_result (convert_type_expr ~substitution type_expr) ~message:(function
        | `Unbound_type_variable var ->
          [%message
            "Unbound type variable when converting type expr in expression"
              (var : string)]
        | `Type_expr_contains_alias type_expr ->
          [%message
            "Constructor type in environment contains alias"
              (type_expr : type_expr)])


  let is_cases_generalized cases =
    let open Computation.Let_syntax in
    let%bind env = env in
    of_result (is_cases_generalized ~env cases) ~message:(function
        | `Unbound_constructor constr ->
        [%message "Constructor is unbound in environment" (constr : string)])


  (* {5 : Inference of expressions} *)

  let inst_constr_decl name
      : (Type.t option * Type.t * unit Constraint.t) Binder.t
    =
    let open Binder.Let_syntax in
    let& constr_alphas, constr_arg, constr_type, constr_constraints =
      let open Computation.Let_syntax in
      let%bind env = env in
      of_result
        (inst_constr_decl ~flexibility:Flexible ~env name)
        ~message:(function
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
    let%bind () = exists_vars constr_alphas in
    let%bind constr_arg =
      match constr_arg with
      | Some (constr_betas, constr_arg) ->
        let%bind () = exists_vars constr_betas in
        return (Some constr_arg)
      | None -> return None
    in
    return (constr_arg, constr_type, constr_constraints)


  let inst_label_decl label : (Type.t * Type.t) Binder.t =
    let open Binder.Let_syntax in
    let& vars, label_arg, label_type =
      let open Computation.Let_syntax in
      let%bind env = env in
      (* Determine the label details from the environment *)
      let%bind { label_arg; label_type; label_type_params; _ } =
        of_result
          (Env.find_label env label)
          ~message:(fun (`Unbound_label label) ->
            [%message "Label is unbound in environment" (label : string)])
      in
      (* Compute a fresh set of existential variables *)
      let%bind substitution =
        of_result
          (Substitution.of_alist
             (List.map
                ~f:(fun x -> x, (fresh (), Substitution.Flexible))
                label_type_params))
          ~message:(fun (`Duplicate_type_variable var) ->
            [%message
              "Duplicate type parameter in label in environment"
                (var : string)
                (label : string)])
      in
      (* Compute the inferred type using the existential variables. *)
      let%bind label_arg = convert_type_expr ~substitution label_arg in
      let%bind label_type = convert_type_expr ~substitution label_type in
      return (Substitution.rng substitution, label_arg, label_type)
    in
    let%bind () = exists_vars vars in
    return (label_arg, label_type)


  let infer_constr constr_name constr_type
      : (constructor_description Constraint.t * Type.t option) Binder.t
    =
    let open Binder.Let_syntax in
    (* Instantiate the constructor description. *)
    let%bind constr_arg, constr_type', constr_constraints =
      inst_constr_decl constr_name
    in
    (* Build constraint. *)
    let constr_desc =
      constr_type
      =~ constr_type'
      >> constr_constraints
      >> make_constr_desc constr_name constr_arg constr_type
    in
    return (constr_desc, constr_arg)


  let infer_label label label_type
      : (label_description Constraint.t * Type.t) Binder.t
    =
    let open Binder.Let_syntax in
    let%bind label_arg, label_type' = inst_label_decl label in
    (* Convert to variables *)
    let label_desc =
      label_type =~ label_type' >> make_label_desc label label_arg label_type
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
    let& fragment, pat = Pattern.Non_generalized.infer_pat pat pat_type in
    let alphas, bindings = Fragment.Non_generalized.to_bindings fragment in
    let%bind () = exists_vars alphas in
    return (bindings, pat)


  let make_exp_desc_forall vars var exp_desc exp_type =
    let open Constraint.Let_syntax in
    let internal_name = "@dromedary.internal.pexp_forall" in
    let%map term_let_bindings, _ =
      let_
        ~bindings:
          [ ((vars, [ var ]) @. exp_desc)
            @=> [ internal_name #= (Type.var var) ]
          ]
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
          (let%map () = exp_type =~ infer_primitive prim in
           Texp_prim prim)
      | Pexp_const const ->
        return
          (let%map () = exp_type =~ infer_constant const in
           Texp_const const)
      | Pexp_fun (pat, exp) ->
        let@ var1 = exists () in
        let@ var2 = exists () in
        let@ bindings, pat = infer_pat pat (Type.var var1) in
        let%bind exp = infer_exp exp (Type.var var2) in
        return
          (let%map () = exp_type =~ Type.var var1 @-> Type.var var2
           and pat = pat
           and exp = def ~bindings ~in_:exp in
           Texp_fun (pat, exp))
      | Pexp_app (exp1, exp2) ->
        let@ var = exists () in
        let%bind exp1 = infer_exp exp1 (Type.var var @-> exp_type) in
        let%bind exp2 = infer_exp exp2 (Type.var var) in
        return
          (let%map exp1 = exp1
           and exp2 = exp2 in
           Texp_app (exp1, exp2))
      | Pexp_constraint (exp, exp_type') ->
        let%bind exp_type' = convert_core_type exp_type' in
        let%bind exp_desc = infer_exp_desc exp exp_type' in
        return
          (let%map () = exp_type =~ exp_type'
           and exp_desc = exp_desc in
           exp_desc)
      | Pexp_tuple exps ->
        let@ vars, exps = infer_exps exps in
        return
          (let%map () = exp_type =~ tuple (List.map ~f:Type.var vars)
           and exps = exps in
           Texp_tuple exps)
      | Pexp_match (match_exp, cases) ->
        if%bind is_cases_generalized cases
        then (
          match match_exp with
          | Pexp_constraint (match_exp, match_exp_type) ->
            if%bind is_rigid_annotation match_exp_type
            then (
              (* GADT MATCH! *)
              (* Determine the bound rigid variables in the annotation. *)
              let%bind gammas =
                free_variables_of_core_type match_exp_type
                |> List.map ~f:find_var
                |> all
              in
              (* Convert the annotation to a constraint type *)
              let%bind match_exp_type = convert_core_type match_exp_type in
              (* Infer the expression *)
              let%bind match_exp = infer_exp match_exp match_exp_type in
              let%bind cases =
                infer_generalized_cases gammas match_exp_type cases exp_type
              in
              return
                (let%map match_exp = match_exp
                 and match_exp_type = decode match_exp_type
                 and cases = cases in
                 Texp_match (match_exp, match_exp_type, cases)))
            else
              fail
                [%message
                  "Cannot pattern match on generalized cases without a rigid \
                   annotation"]
          | _ ->
            fail
              [%message
                "Cannot pattern match on generalized cases without a annotation"])
        else
          let@ var = exists () in
          let%bind match_exp = infer_exp match_exp (Type.var var) in
          let%bind cases = infer_cases cases (Type.var var) exp_type in
          return
            (let%map match_exp = match_exp
             and match_exp_type = decode (Type.var var)
             and cases = cases in
             Texp_match (match_exp, match_exp_type, cases))
      | Pexp_ifthenelse (if_exp, then_exp, else_exp) ->
        let%bind if_exp = infer_exp if_exp bool in
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
          ~flexibility:Flexible
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
          ~flexibility:Rigid
          ~f:(fun vars ->
            let var = fresh () in
            let%bind exp_desc = infer_exp_desc exp (Type.var var) in
            return (make_exp_desc_forall vars var exp_desc exp_type))
          ~message:(fun var ->
            [%message
              "Duplicate variable in universal quantifier (forall)"
                (exp : Parsetree.expression)
                (var : string)])
      | Pexp_field (exp, label) ->
        let@ var = exists () in
        let%bind exp = infer_exp exp (Type.var var) in
        let%bind label_desc = inst_label label exp_type (Type.var var) in
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
      | Pexp_let (Nonrecursive, value_bindings, exp) ->
        (* TODO: Coercion! *)
        let%bind let_bindings = infer_value_bindings value_bindings in
        let%bind exp = infer_exp exp exp_type in
        let to_value_binding (_, (variables, (pat, exp))) =
          { tvb_pat = pat; tvb_expr = variables, exp }
        in
        return
          (let%map let_bindings, exp = let_ ~bindings:let_bindings ~in_:exp in
           Texp_let (List.map ~f:to_value_binding let_bindings, exp))
      | Pexp_let (Recursive, rec_value_bindings, exp) ->
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
    and infer_generalized_cases gammas pat_type cases exp_type
        : Typedtree.case list Constraint.t Computation.t
      =
      let open Computation.Let_syntax in
      let infer_case { pc_lhs = pat; pc_rhs = exp }
          : Typedtree.case Constraint.t Computation.t
        =
        let%bind pat' = Pattern.Generalized.infer_pat pat gammas pat_type in
        let%bind fragment = Pattern.Generalized.infer_fragment pat pat_type in
        let betas, constraint_, bindings =
          Fragment.Generalized.to_bindings fragment
        in
        let%bind exp = infer_exp exp exp_type in
        return
          (let%map tc_lhs = pat'
           and _, (), tc_rhs =
             (gammas @ betas) #. constraint_ #=> (def ~bindings ~in_:exp)
           in
           { tc_lhs; tc_rhs })
      in
      let%bind cases = List.map ~f:infer_case cases |> all in
      return (Constraint.all cases)
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
            let& exp = infer_exp exp (Type.var var) in
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
            let%bind exp = infer_exp exp (Type.var var) in
            let%bind label_desc = inst_label label (Type.var var) exp_type in
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
    and infer_value_binding
        { pvb_vars = rigid_vars; pvb_pat = pat; pvb_expr = exp }
        : (Typedtree.pattern * Typedtree.expression) let_binding Computation.t
      =
      let open Computation.Let_syntax in
      extend_substitution
        rigid_vars
        ~flexibility:Rigid
        ~f:(fun rigid_vars ->
          let var = fresh () in
          let%bind fragment, pat =
            Pattern.Non_generalized.infer_pat pat (Type.var var)
          in
          let alphas, bindings =
            Fragment.Non_generalized.to_bindings fragment
          in
          let%bind exp = infer_exp exp (Type.var var) in
          return (((rigid_vars, var :: alphas) @. (pat &~ exp)) @=> bindings))
        ~message:(fun var ->
          [%message
            "Duplicate variable in forall quantifier (let)" (var : string)])
    and infer_rec_value_binding value_binding
        : Typedtree.expression let_rec_binding Computation.t
      =
      let open Computation.Let_syntax in
      let%bind annotation =
        of_result
          (annotation_of_rec_value_binding value_binding)
          ~message:(function `Invalid_recursive_binding ->
            [%message "Invalid recursive value binding form."])
      in
      match annotation with
      | `Annotated (rigid_vars, f, exp, annotation) ->
        extend_substitution
          rigid_vars
          ~flexibility:Rigid
          ~f:(fun rigid_vars ->
            let%bind annotation = convert_core_type annotation in
            let%bind exp = infer_exp exp annotation in
            return (rigid_vars, exp) #~> (f #= annotation))
          ~message:(fun var ->
            [%message
              "Duplicate variable in forall quantifier (let)" (var : string)])
      | `Unannotated (rigid_vars, f, exp) ->
        extend_substitution
          rigid_vars
          ~flexibility:Rigid
          ~f:(fun rigid_vars ->
            let var = fresh () in
            let%bind exp = infer_exp exp (Type.var var) in
            return (((rigid_vars, [ var ]) @. exp) @~> (f #= (Type.var var))))
          ~message:(fun var ->
            [%message
              "Duplicate variable in forall quantifier (let)" (var : string)])
    in
    infer_exp exp exp_type


  let infer exp =
    let open Computation.Let_syntax in
    let@ var = exists () in
    infer_exp exp (Type.var var)
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
