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
let exn = Type_former.Constr ([], "exn")
let exn_ = Type.former exn
let ref x = Type_former.Constr ([ x ], "ref")
let ref_ x = Type.former (ref x)

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


(* [substitution_of_vars vars] returns a substitution w/ 
   domain [vars] bound to fresh variables. *)
let substitution_of_vars vars =
  Substitution.of_alist (List.map ~f:(fun x -> x, fresh ()) vars)


(* [inst_constr_decl ~env constr] instantiates a constructor declaration w/ constructor name [constr] *)
let inst_constr_decl ~env name
    : ( variable list
        * (variable list * Type.t) option
        * Type.t
        * (Constraint.Type.t * Constraint.Type.t) list
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
    substitution_of_vars vars
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
  let%bind constr_constraint =
    List.map constr_constraints ~f:(fun (type1, type2) ->
        let%bind type1 = convert_type_expr ~substitution type1 in
        let%bind type2 = convert_type_expr ~substitution type2 in
        return (type1, type2))
    |> Result.all
  in
  return (alphas, constr_arg, constr_type, constr_constraint)


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
      | Some (_, pat) -> is_pat_generalized ~env pat
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


(* {3 : Polymorphic recursion functions} *)

let rec find_annotation exp =
  let open Option.Let_syntax in
  match exp with
  | Pexp_constraint (_, type_) -> return type_
  | Pexp_fun (Ppat_constraint (_, type1), exp') ->
    let%bind type2 = find_annotation exp' in
    return (Ptyp_arrow (type1, type2))
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
    let%map core_type = find_annotation exp in
    value_binding, core_type


let annotation_of_rec_value_binding value_binding
    : ( [ `Annotated of string list * string * Parsetree.expression * core_type
        | `Unannotated of string list * string * Parsetree.expression
        ]
    , _ ) Result.t
  =
  let open Result in
  let open Let_syntax in
  match annotation_of_value_binding value_binding with
  | Some
      ({ pvb_forall_vars = forall_vars; pvb_pat = pat; pvb_expr = exp }, type_)
    ->
    (match pat with
    | Ppat_var term_var ->
      return (`Annotated (forall_vars, term_var, exp, type_))
    | _ -> fail `Invalid_recursive_binding)
  | None ->
    (match value_binding.pvb_pat with
    | Ppat_var term_var ->
      return
        (`Unannotated
          (value_binding.pvb_forall_vars, term_var, value_binding.pvb_expr))
    | _ -> fail `Invalid_recursive_binding)


(** {4: Value restriction} *)

let rec is_non_expansive exp = 
  match exp with
  | Pexp_var _ | Pexp_const _ | Pexp_prim _ | Pexp_fun _ -> true
  | Pexp_construct (_, Some exp) -> is_non_expansive exp
  | Pexp_construct (_, None) -> true
  | Pexp_forall (_, exp) | Pexp_exists (_, exp) | Pexp_constraint (exp, _) | Pexp_let (Recursive, _, exp)   -> is_non_expansive exp
  | Pexp_record label_exps -> List.for_all label_exps ~f:(fun (_, exp) -> is_non_expansive exp)
  | Pexp_tuple exps -> List.for_all exps ~f:is_non_expansive
  | Pexp_sequence (exp1, exp2) -> is_non_expansive exp1 && is_non_expansive exp2
  | Pexp_let _ | Pexp_match _ | Pexp_ifthenelse _ | Pexp_app _ | Pexp_while _ | Pexp_for _ | Pexp_try _ | Pexp_field _ -> false


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


  let inst_constr_decl name
      : ((variable list * Type.t) option
        * Type.t
        * (Constraint.Type.t * Constraint.Type.t) list)
      Binder.t
    =
    let open Binder.Let_syntax in
    let& alphas, constr_arg, constr_type, constr_constraint =
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
    let%bind () = exists_vars alphas in
    return (constr_arg, constr_type, constr_constraint)


  let infer_constr constr_name constr_type
      : (constructor_description Constraint.t
        * (variable list * variable) option
        * (Constraint.Type.t * Constraint.Type.t) list)
      Binder.t
    =
    let open Binder.Let_syntax in
    (* Instantiate the constructor description. *)
    let%bind constr_arg, constr_type', constr_constraint =
      inst_constr_decl constr_name
    in
    (* Convert [const_arg] and [const_type'] to variables *)
    let%bind constr_arg =
      match constr_arg with
      | Some (constr_betas, constr_arg) ->
        let%bind () = forall_vars constr_betas in
        let%bind constr_arg = of_type constr_arg in
        return (Some (constr_betas, constr_arg))
      | None -> return None
    in
    let%bind constr_type' = of_type constr_type' in
    (* Build constraint. *)
    let constr_desc =
      constr_type
      =~ constr_type'
      >> make_constr_desc constr_name Option.(constr_arg >>| snd) constr_type
    in
    return (constr_desc, constr_arg, constr_constraint)


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
      | Ppat_construct (constr, arg_pat) ->
        let@ constr_desc, arg_pat_type, constr_constraint =
          infer_constr constr pat_type
        in
        let%bind () = assert_ constr_constraint in
        let%bind arg_pat =
          match arg_pat, arg_pat_type with
          | Some (betas, arg_pat), Some (constr_betas, arg_pat_type) ->
            if List.is_empty betas
            then (
              let%bind pat = infer_pat arg_pat arg_pat_type in
              return (constr_constraint #=> pat >>| Option.some))
            else (
              match List.zip betas constr_betas with
              | Ok alist ->
                let%bind substitution =
                  of_result
                    (Substitution.of_alist alist)
                    ~message:(fun (`Duplicate_type_variable var) ->
                      [%message
                        "Duplicate type variable in constructor existentials"
                          (var : string)])
                in
                let%bind () = extend_fragment_substitution substitution in
                extend_substitution
                  ~substitution
                  (let%bind pat = infer_pat arg_pat arg_pat_type in
                   return (constr_constraint #=> pat >>| Option.some))
              | Unequal_lengths ->
                fail
                  [%message
                    "Constructor existential variable mistmatch with \
                     definition."])
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
      | Ppat_constraint (pat, pat_type') ->
        let@ pat_type1 =
          let open Binder.Let_syntax in
          let& pat_type' = convert_core_type pat_type' in
          of_type pat_type'
        in
        let@ pat_type2 =
          let open Binder.Let_syntax in
          let& pat_type' = convert_core_type pat_type' in
          of_type pat_type'
        in
        let%bind pat_desc = infer_pat_desc pat pat_type2 in
        return
          (let%map () = pat_type =~ pat_type1
           and pat_desc = pat_desc in
           pat_desc)
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
  let extend_substitution_vars vars ~f ~message =
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


  let inst_constr_decl name
      : (Type.t option * Type.t * (Constraint.Type.t * Constraint.Type.t) list)
      Binder.t
    =
    let open Binder.Let_syntax in
    let& constr_alphas, constr_arg, constr_type, constr_constraints =
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
    let%bind () = exists_vars constr_alphas in
    let%bind constr_arg =
      match constr_arg with
      | Some (constr_betas, constr_arg) ->
        let%bind () = forall_vars constr_betas in
        return (Some constr_arg)
      | None -> return None
    in
    return (constr_arg, constr_type, constr_constraints)


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


  let ( -~- ) type1 type2 : unit Constraint.t =
    let bindings1, var1 = Shallow_type.of_type type1 in
    let bindings2, var2 = Shallow_type.of_type type2 in
    Constraint.exists (bindings1 @ bindings2) (var1 =~ var2)


  let infer_constr constr_name constr_type
      : (constructor_description Constraint.t * variable option) Binder.t
    =
    let open Binder.Let_syntax in
    (* Instantiate the constructor description. *)
    let%bind constr_arg, constr_type', constr_constraint =
      inst_constr_decl constr_name
    in
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
      >> Constraint.all_unit
           (List.map constr_constraint ~f:(fun (t1, t2) -> t1 -~- t2))
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
      : (Shallow_type.binding list
        * binding list
        * Typedtree.pattern Constraint.t
        * (Constraint.Type.t * Constraint.Type.t) list
        * Substitution.t)
      Binder.t
    =
    let open Binder.Let_syntax in
    (* print_endline
      (Sexp.to_string_hum [%message "infer_pat" (pat : Parsetree.pattern)]); *)
    let& fragment, pat = Pattern.infer pat pat_type in
    let ( universal_bindings
        , existential_bindings
        , local_constraint
        , term_bindings
        , substitution )
      =
      Fragment.to_bindings fragment
    in
    let%bind () = forall_vars universal_bindings in
    return
      (existential_bindings, term_bindings, pat, local_constraint, substitution)


  let infer_primitive prim prim_type : unit Constraint.t Computation.t =
    let open Computation.Let_syntax in
    match prim with
    | Prim_add | Prim_sub | Prim_div | Prim_mul ->
      return (prim_type =~- int_ @--> int_ @--> int_)
    | Prim_eq -> return (prim_type =~- int_ @--> int_ @--> bool_)
    | Prim_ref ->
      let@ var = exists () in
      let var = Type.var var in
      return (prim_type =~- var @--> ref_ var)
    | Prim_deref ->
      let@ var = exists () in
      let var = Type.var var in
      return (prim_type =~- ref_ var @--> var)
    | Prim_assign ->
      let@ var = exists () in
      let var = Type.var var in
      return (prim_type =~- ref_ var @--> var @--> unit_)


  let bind_pat pat pat_type ~in_ : (Typedtree.pattern * _) Constraint.t Binder.t
    =
    let open Binder.Let_syntax in
    let%bind existential_bindings, bindings, pat, local_constraint, substitution
      =
      infer_pat pat pat_type
    in
    let& in_ = extend_substitution ~substitution in_ in
    return
      (let%map pats, in_ =
         let_
           ~bindings:
             [ ((([], existential_bindings) @. pat) @=> (true, bindings))
                 local_constraint
             ]
           ~in_
       in
       let pat =
         match pats with
         | [ (_, (_, pat)) ] -> pat
         | _ -> assert false
       in
       pat, in_)


  let make_exp_desc_forall vars var exp_desc exp_type =
    let open Constraint.Let_syntax in
    let internal_name = "@dromedary.internal.pexp_forall" in
    let%map term_let_bindings, _ =
      let_
        ~bindings:
          [ (((vars, [ var, None ]) @. exp_desc) @=> (true, [ internal_name #= var ]))
              []
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
        let%bind constraint_ = infer_primitive prim exp_type in
        return
          (let%map () = constraint_ in
           Texp_prim prim)
      | Pexp_const const ->
        return
          (let%map () = exp_type =~- infer_constant const in
           Texp_const const)
      | Pexp_fun (pat, exp) ->
        let@ var1 = exists () in
        let@ var2 = exists () in
        let@ pat_exp = bind_pat pat var1 ~in_:(infer_exp exp var2) in
        return
          (let%map () = exp_type =~= var1 @-> var2
           and pat, exp = pat_exp in
           Texp_fun (pat, exp))
      | Pexp_app (exp1, exp2) ->
        let@ var = exists () in
        let%bind exp1 = lift (infer_exp exp1) (var @-> exp_type) in
        let%bind exp2 = infer_exp exp2 var in
        return
          (let%map exp1 = exp1
           and exp2 = exp2 in
           Texp_app (exp1, exp2))
      | Pexp_constraint (Pexp_match (match_exp, cases), exp_type') ->
        let annotate_case case =
          { case with pc_rhs = Pexp_constraint (case.pc_rhs, exp_type') }
        in
        infer_exp_desc
          (Pexp_match (match_exp, List.map ~f:annotate_case cases))
          exp_type
      | Pexp_constraint (exp, exp_type') ->
        let%bind exp_type' = convert_core_type exp_type' in
        let@ exp_type1 = of_type exp_type' in
        let@ exp_type2 = of_type exp_type' in
        let%bind exp_desc = infer_exp_desc exp exp_type1 in
        return
          (let%map () = exp_type =~ exp_type2
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
        extend_substitution_vars
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
        extend_substitution_vars
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
      | Pexp_try (exp, cases) ->
        let%bind exp = infer_exp exp exp_type in
        let@ exn = of_type exn_ in
        let%bind cases = infer_cases cases exn exp_type in
        return
          (let%map exp = exp
           and cases = cases in
           Texp_try (exp, cases))
      | Pexp_sequence (exp1, exp2) ->
        let%bind exp1 = lift (infer_exp exp1) unit in
        let%bind exp2 = infer_exp exp2 exp_type in
        return
          (let%map exp1 = exp1
           and exp2 = exp2 in
           Texp_sequence (exp1, exp2))
      | Pexp_while (exp1, exp2) ->
        let%bind exp1 = lift (infer_exp exp1) bool in
        let%bind exp2 = lift (infer_exp exp2) unit in
        return
          (let%map () = exp_type =~= unit
           and exp1 = exp1
           and exp2 = exp2 in
           Texp_while (exp1, exp2))
      | Pexp_for (pat, exp1, exp2, direction_flag, exp3) ->
        let%bind index =
          match pat with
          | Ppat_any -> return "_for"
          | Ppat_var x -> return x
          | _ ->
            fail [%message "Invalid for loop index" (pat : Parsetree.pattern)]
        in
        let%bind exp1 = lift (infer_exp exp1) int in
        let%bind exp2 = lift (infer_exp exp2) int in
        let%bind exp3 = lift (infer_exp exp3) unit in
        let@ int = of_type int_ in
        return
          (let%map () = exp_type =~= unit
           and exp1 = exp1
           and exp2 = exp2
           and exp3 = def ~bindings:[ index #= int ] ~in_:exp3 in
           Texp_for (index, exp1, exp2, direction_flag, exp3))
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
            let@ pat_exp =
              bind_pat pc_lhs lhs_type ~in_:(infer_exp pc_rhs rhs_type)
            in
            return
              (let%map pat, exp = pat_exp in
               { tc_lhs = pat; tc_rhs = exp }))
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
    and infer_value_binding
        { pvb_forall_vars = forall_vars; pvb_pat = pat; pvb_expr = exp }
        : (Typedtree.pattern * Typedtree.expression) let_binding Computation.t
      =
      let open Computation.Let_syntax in
      extend_substitution_vars
        forall_vars
        ~f:(fun forall_vars ->
          let var = fresh () in
          let%bind fragment, pat = Pattern.infer pat var in
          let ( universal_bindings
              , existential_bindings
              , local_constraint
              , bindings
              , _substitution )
            =
            Fragment.to_bindings fragment
          in
          (* Temporary: TODO: Figure out how to merge universals w/ new lets. *)
          assert (List.is_empty universal_bindings);
          let is_non_expansive = is_non_expansive exp in
          let%bind exp = infer_exp exp var in
          return
            ((((forall_vars, (var, None) :: existential_bindings)
              @. (pat &~ exp))
             @=> (is_non_expansive, bindings))
               local_constraint))
        ~message:(fun var ->
          [%message
            "Duplicate variable in universal quantifier (let)"
              (exp : Parsetree.expression)
              (var : string)])
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
      | `Annotated (forall_vars, f, exp, annotation) ->
        extend_substitution_vars
          forall_vars
          ~f:(fun forall_vars ->
            let%bind annotation = convert_core_type annotation in
            let annotation_bindings, annotation =
              Shallow_type.of_type annotation
            in
            let%bind exp = infer_exp exp annotation in
            return
              ((forall_vars, annotation_bindings) @. exp) #~> (f #= annotation))
          ~message:(fun var ->
            [%message
              "Duplicate variable in forall quantifier (let)" (var : string)])
      | `Unannotated (forall_vars, f, exp) ->
        extend_substitution_vars
          forall_vars
          ~f:(fun forall_vars ->
            let var = fresh () in
            let%bind exp = infer_exp exp var in
            return (((forall_vars, [ var, None ]) @. exp) @~> (f #= var)))
          ~message:(fun var ->
            [%message
              "Duplicate variable in forall quantifier (let)" (var : string)])
    in
    infer_exp exp exp_type


  let infer exp : Typedtree.expression Constraint.t Computation.t =
    let open Computation.Let_syntax in
    let@ var = exists () in
    infer_exp exp var
end

let let_0 ~in_ =
  let_ ~bindings:[ ((([], []) @. in_) @=> (true, [])) [] ] ~in_:(return ())
  >>| function
  | [ ([], (vars, t)) ], _ -> vars, t
  | _ -> assert false


let solve ?(debug = false) ~abbrevs cst =
  solve ~debug ~abbrevs cst
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
             "Rigid type variable escaped when generalizing" (var : string)]
         | `Cannot_flexize var ->
           [%message
             "Could not flexize rigid type variable when generalizing"
               (var : string)]
         | `Scope_escape type_expr ->
           [%message
             "Type escape it's equational scope" (type_expr : type_expr)]
         | `Inconsistent_equations ->
           [%message "Inconsistent equations added by local branches"]
         | `Non_rigid_equations -> [%message "Non rigid equations"])


let infer ?(debug = false) exp ~env:env' ~abbrevs =
  let open Result.Let_syntax in
  let%bind exp =
    let[@landmark] exp = Expression.infer exp in
    Computation.Expression.(run ~env:env' (exp >>| fun in_ -> let_0 ~in_))
  in
  solve ~debug ~abbrevs exp
