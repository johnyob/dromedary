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
let float = Type_former.Constr ([], "float")
let float_ = Type.former float
let char = Type_former.Constr ([], "char")
let char_ = Type.former char
let string = Type_former.Constr ([], "string")
let string_ = Type.former string
let exn = Type_former.Constr ([], "exn")
let exn_ = Type.former exn
let ref x = Type_former.Constr ([ x ], "ref")
let ref_ x = Type.former (ref x)
let variant t = Type_former.Variant t
let variant_ t = Type.former (variant t)
let row_cons label t1 t2 = Type.Row_cons (label, t1, t2)
let row_uniform t = Type.Row_uniform t
let some x = Type_former.Constr ([ x ], "some")
let some_ x = Type.former (some x)
let none = Type_former.Constr ([], "none")
let none_ = Type.former none

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
  (* | Ptyp_alias (t, x) ->
    let var = fresh () in
    let substitution = Substitution.add substitution x var in
    let%bind t = convert_core_type ~substitution t in
    return (Type.Mu (var, t)) *)
  | Ptyp_variant row ->
    let%bind row = convert_row ~substitution row in
    return (variant_ row)
  | Ptyp_row_cons (tag, t, row) ->
    let%bind t = convert_core_type ~substitution t in
    let%bind row = convert_row ~substitution row in
    return (row_cons tag (some_ t) row)
  | Ptyp_row_empty -> return (row_uniform none_)


and convert_row ~substitution row = convert_core_type ~substitution row

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
  | Ttyp_variant t ->
    let%bind t = convert_row ~substitution t in
    return (variant_ t)
  | _ -> fail (`Type_expr_is_ill_sorted type_expr)


and convert_row ~substitution row : (Type.t, _) Result.t =
  let open Result in
  let open Let_syntax in
  match row with
  | Ttyp_row_cons (label, t1, t2) ->
    let%bind t1 = convert_type_expr ~substitution t1 in
    let%bind t2 = convert_row ~substitution t2 in
    return (row_cons label t1 t2)
  | Ttyp_row_uniform t ->
    let%bind t = convert_type_expr ~substitution t in
    return (row_uniform t)
  | _ -> fail (`Type_expr_is_ill_sorted row)


(* [infer_constant const] returns the type of [const]. *)
let infer_constant const : Type.t =
  match const with
  | Const_int _ -> int_
  | Const_bool _ -> bool_
  | Const_float _ -> float_
  | Const_char _ -> char_
  | Const_string _ -> string_
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
    : ( Constraint.variable list * Constraint.variable list * Type.t * Type.t, _
    ) Result.t
  =
  let open Result.Let_syntax in
  let%bind { label_arg; label_type; label_alphas; label_betas; _ } =
    Env.find_label env label
  in
  (* Redefined due to repeated error function *)
  let substitution_of_vars vars =
    substitution_of_vars vars
    |> Result.map_error ~f:(fun (`Duplicate_type_variable var) ->
           `Duplicate_type_parameter_for_label (label, var))
  in
  (* Compute a fresh set of existential variables *)
  let%bind substitution = substitution_of_vars label_alphas in
  let alphas = Substitution.rng substitution in
  let%bind substitution' = substitution_of_vars label_betas in
  let betas = Substitution.rng substitution' in
  let substitution = Substitution.merge substitution substitution' in
  (* Compute the inferred type using the existential variables. *)
  let%bind label_arg = convert_type_expr ~substitution label_arg in
  let%bind label_type = convert_type_expr ~substitution label_type in
  return (alphas, betas, label_arg, label_type)


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
  | Ppat_variant (_, pat) ->
    (match pat with
    | Some pat -> is_pat_generalized ~env pat
    | None -> return false)
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
  | Pexp_construct (_, Some exp) | Pexp_variant (_, Some exp) ->
    is_non_expansive exp
  | Pexp_construct (_, None) | Pexp_variant (_, None) -> true
  | Pexp_forall (_, exp)
  | Pexp_exists (_, exp)
  | Pexp_constraint (exp, _)
  | Pexp_let (Recursive, _, exp) -> is_non_expansive exp
  | Pexp_record label_exps ->
    List.for_all label_exps ~f:(fun (_, exp) -> is_non_expansive exp)
  | Pexp_tuple exps -> List.for_all exps ~f:is_non_expansive
  | Pexp_sequence (exp1, exp2) -> is_non_expansive exp1 && is_non_expansive exp2
  | Pexp_let _
  | Pexp_match _
  | Pexp_ifthenelse _
  | Pexp_app _
  | Pexp_while _
  | Pexp_for _
  | Pexp_try _
  | Pexp_field _ -> false


(** {5: Polymorphic variants} *)

type variant_pattern = Vpat_variant of tag * Parsetree.pattern option

type variant_default_pattern =
  | Vpat_any
  | Vpat_var of string

type variant_case =
  { vc_lhs : variant_pattern
  ; vc_rhs : Parsetree.expression
  }

type variant_default_case =
  { vdc_lhs : variant_default_pattern
  ; vdc_rhs : Parsetree.expression
  }

type variant_cases =
  { cases : variant_case list
  ; default_case : variant_default_case option
  }

let variant_default_case_of_case : Parsetree.case -> variant_default_case option
  =
 fun { pc_lhs = pat; pc_rhs = exp } ->
  match pat with
  | Ppat_any -> Some { vdc_lhs = Vpat_any; vdc_rhs = exp }
  | Ppat_var x -> Some { vdc_lhs = Vpat_var x; vdc_rhs = exp }
  | _ -> None


let variant_case_of_case : Parsetree.case -> variant_case option =
 fun { pc_lhs = pat; pc_rhs = exp } ->
  match pat with
  | Ppat_variant (tag, pat) ->
    Some { vc_lhs = Vpat_variant (tag, pat); vc_rhs = exp }
  | _ -> None


let rec variant_cases_of_cases : Parsetree.case list -> variant_cases option =
 fun cases ->
  let open Option.Let_syntax in
  match cases with
  | [] -> None
  | [ case ] ->
    let%map case = variant_case_of_case case in
    { cases = [ case ]; default_case = None }
  | [ case1; case2 ] ->
    let%map case = variant_case_of_case case1 in
    (match variant_case_of_case case2 with
    | Some case' -> { cases = [ case; case' ]; default_case = None }
    | None ->
      let default_case = variant_default_case_of_case case2 in
      { cases = [ case ]; default_case })
  | case :: cases ->
    (* invairant: len cases >= 2 *)
    let%bind case = variant_case_of_case case in
    let%map cases = variant_cases_of_cases cases in
    { cases with cases = case :: cases.cases }


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
                (var : string)]
          | `Type_expr_is_ill_sorted type_expr ->
            [%message
              "Type expression is not correctly sorted" (type_expr : type_expr)])
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
        let%bind () = forall_ctx ~ctx:constr_betas in
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
          (let%map () = pat_type =~= Former (tuple vars)
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
      | Ppat_variant _ ->
        fail
          [%message
            "Deep pattern matching for polymorphic variants not supported!"]
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


  let infer_variant_default_pat variant_default_pat pat_type default_pat_type =
    let rec infer_pat pat pat_type
        : Typedtree.pattern Constraint.t Computation.t
      =
      let open Computation.Let_syntax in
      let%bind pat_desc = infer_pat_desc pat in
      return
        (let%map pat_desc = pat_desc
         and pat_type = decode pat_type in
         { pat_desc; pat_type })
    and infer_pat_desc pat : Typedtree.pattern_desc Constraint.t Computation.t =
      let open Computation.Let_syntax in
      match pat with
      | Vpat_any -> const Tpat_any
      | Vpat_var x ->
        let%bind () = extend x default_pat_type in
        const (Tpat_var x)
    in
    Computation.run (infer_pat variant_default_pat pat_type)
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
    return (Constraint.exists ~ctx:([ var ], [ var, shallow_type ]) t)


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
                (var : string)]
          | `Type_expr_is_ill_sorted type_expr ->
            [%message
              "Type expression is not correctly sorted" (type_expr : type_expr)])
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


  let inst_label_decl label
      : (Constraint.variable list * Constraint.variable list * Type.t * Type.t)
      Computation.t
    =
    let open Computation.Let_syntax in
    let%bind env = env in
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
              (var : string)]
        | `Type_expr_is_ill_sorted type_expr ->
          [%message
            "Type expression is not correctly sorted" (type_expr : type_expr)])


  let ( -~- ) type1 type2 : unit Constraint.t =
    let ctx1, var1 = Shallow_type.of_type type1 in
    let ctx2, var2 = Shallow_type.of_type type2 in
    Constraint.exists ~ctx:(Shallow_type.Ctx.merge ctx1 ctx2) (var1 =~ var2)


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
    let& label_alphas, label_betas, label_arg, label_type' =
      inst_label_decl label
    in
    let%bind () = exists_vars (label_alphas @ label_betas) in
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
      : (existential_context
        * equations
        * binding list
        * Typedtree.pattern Constraint.t
        * Substitution.t)
      Binder.t
    =
    let open Binder.Let_syntax in
    (* print_endline
      (Sexp.to_string_hum [%message "infer_pat" (pat : Parsetree.pattern)]); *)
    let& fragment, pat = Pattern.infer pat pat_type in
    let universal_ctx, existential_ctx, equations, term_bindings, substitution =
      Fragment.to_bindings fragment
    in
    let%bind () = forall_ctx ~ctx:universal_ctx in
    return (existential_ctx, equations, term_bindings, pat, substitution)


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
    let%bind existential_ctx, equations, bindings, pat, substitution =
      infer_pat pat pat_type
    in
    let& in_ = extend_substitution ~substitution in_ in
    return
      (let%map pats, in_ =
         let_
           ~bindings:
             Binding.
               [ let_
                   ~ctx:([], existential_ctx)
                   ~is_non_expansive:true
                   ~bindings
                   ~in_:pat
                   ~equations
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
          Binding.
            [ let_
                ~ctx:(vars, ([ var ], []))
                ~is_non_expansive:true
                ~bindings:[ internal_name #= var ]
                ~in_:exp_desc
                ~equations:[]
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
          (let%map () = exp_type =~= Former (var1 @-> var2)
           and pat, exp = pat_exp in
           Texp_fun (pat, exp))
      | Pexp_app (exp1, exp2) ->
        let@ var = exists () in
        let%bind exp1 = lift (infer_exp exp1) (Former (var @-> exp_type)) in
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
          (let%map () = exp_type =~= Former (tuple vars)
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
        let%bind if_exp = lift (infer_exp if_exp) (Former bool) in
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
      | Pexp_variant (tag, arg_exp) ->
        let@ rho1 = exists () in
        let@ rho2 = exists () in
        let@ arg_exp_type = exists () in
        let%bind arg_exp =
          match arg_exp with
          | Some arg_exp ->
            let%bind exp = infer_exp arg_exp arg_exp_type in
            return (exp >>| Option.some)
          | None ->
            return
              (let%map () = arg_exp_type =~- unit_ in
               None)
        in
        let variant_desc =
          let%map () =
            rho1
            =~- row_cons tag (some_ (Type.var arg_exp_type)) (Type.var rho2)
          and variant_row = decode rho1 in
          { variant_tag = tag; variant_row }
        in
        return
          (let%map variant_desc = variant_desc
           and () = exp_type =~- variant_ (Type.var rho1)
           and arg_exp = arg_exp in
           Texp_variant (variant_desc, arg_exp))
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
        let%bind exp1 = lift (infer_exp exp1) (Former unit) in
        let%bind exp2 = infer_exp exp2 exp_type in
        return
          (let%map exp1 = exp1
           and exp2 = exp2 in
           Texp_sequence (exp1, exp2))
      | Pexp_while (exp1, exp2) ->
        let%bind exp1 = lift (infer_exp exp1) (Former bool) in
        let%bind exp2 = lift (infer_exp exp2) (Former unit) in
        return
          (let%map () = exp_type =~= Former unit
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
        let%bind exp1 = lift (infer_exp exp1) (Former int) in
        let%bind exp2 = lift (infer_exp exp2) (Former int) in
        let%bind exp3 = lift (infer_exp exp3) (Former unit) in
        let@ int = of_type int_ in
        return
          (let%map () = exp_type =~= Former unit
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
      match variant_cases_of_cases cases with
      | None ->
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
      | Some variant_cases ->
        infer_variant_cases variant_cases lhs_type rhs_type
    and infer_variant_case
        { vc_lhs = Vpat_variant (tag, arg_pat); vc_rhs }
        lhs_type
        rhs_type
        : (tag * variable * Typedtree.case Constraint.t) Binder.t
      =
      let open Binder.Let_syntax in
      let%bind arg_pat_type = exists () in
      let%bind arg_pat_exp =
        match arg_pat with
        | None ->
          let& exp = infer_exp vc_rhs rhs_type in
          return
            (let%map () = arg_pat_type =~- unit_
             and exp = exp in
             None, exp)
        | Some arg_pat ->
          let%bind pat_exp =
            bind_pat arg_pat lhs_type ~in_:(infer_exp vc_rhs rhs_type)
          in
          return
            (let%map pat, exp = pat_exp in
             Some pat, exp)
      in
      let variant_desc =
        let%map variant_row = decode lhs_type in
        { variant_tag = tag; variant_row }
      in
      let case =
        let%map arg_pat, exp = arg_pat_exp
        and variant_desc = variant_desc
        and pat_type = decode lhs_type in
        { tc_lhs = { pat_desc = Tpat_variant (variant_desc, arg_pat); pat_type }
        ; tc_rhs = exp
        }
      in
      return (tag, arg_pat_type, case)
    and infer_variant_default_case
        { vdc_lhs; vdc_rhs }
        default_case_type
        lhs_type
        rhs_type
        : Typedtree.case Constraint.t Computation.t
      =
      let open Computation.Let_syntax in
      let%bind fragment, pat =
        Pattern.infer_variant_default_pat vdc_lhs lhs_type default_case_type
      in
      let ( _universal_ctx
          , existential_ctx
          , _equations
          , term_bindings
          , _substitution )
        =
        Fragment.to_bindings fragment
      in
      (* TODO: Add assertions *)
      let@ () = exists_ctx ~ctx:existential_ctx in
      let%bind exp = infer_exp vdc_rhs rhs_type in
      return
        (let%map pat = pat
         and exp = def ~bindings:term_bindings ~in_:exp in
         { tc_lhs = pat; tc_rhs = exp })
    and infer_variant_cases { cases; default_case } lhs_type rhs_type
        : Typedtree.case list Constraint.t Computation.t
      =
      let open Computation.Let_syntax in
      let@ default_case_type = exists () in
      let@ cases =
        List.map cases ~f:(fun case ->
            infer_variant_case case lhs_type rhs_type)
        |> Binder.all
      in
      let row_type =
        List.fold_right
          cases
          ~init:(Type.var default_case_type)
          ~f:(fun (tag, var, _) row -> row_cons tag (Type.var var) row)
      in
      let cases =
        List.map cases ~f:(fun (_, _, case) -> case) |> Constraint.all
      in
      let%bind default_case =
        match default_case with
        | None ->
          return
            (let%map () = default_case_type =~- row_uniform none_ in
             None)
        | Some default_case ->
          let%bind default_case =
            infer_variant_default_case
              default_case
              default_case_type
              lhs_type
              rhs_type
          in
          return
            (let%map default_case = default_case in
             Some default_case)
      in
      return
        (let%map () = lhs_type =~- variant_ row_type
         and cases = cases
         and default_case = default_case in
         match default_case with
         | None -> cases
         | Some default_case -> cases @ [ default_case ])
    and infer_label_exps label_exps exp_type
        : (label_description * Typedtree.expression) list Constraint.t
        Computation.t
      =
      let open Computation.Let_syntax in
      let%bind label_exps =
        List.map label_exps ~f:(fun (label, exp) ->
            let%bind label_alphas, label_betas, label_arg, label_type =
              inst_label_decl label
            in
            let@ () = exists_vars label_alphas in
            let@ () = forall_ctx ~ctx:label_betas in
            let@ label_arg = of_type label_arg in
            let@ label_type = of_type label_type in
            let%bind exp = infer_exp exp label_arg in
            let label_desc =
              exp_type
              =~ label_type
              >> make_label_desc label label_arg label_type
            in
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
          let universal_ctx, existential_ctx, equations, bindings, _substitution
            =
            Fragment.to_bindings fragment
          in
          (* Temporary: TODO: Figure out how to merge universals w/ new lets. *)
          assert (List.is_empty universal_ctx);
          let is_non_expansive = is_non_expansive exp in
          let%bind exp = infer_exp exp var in
          return
            (Binding.let_
               ~ctx:
                 ( forall_vars
                 , Shallow_type.Ctx.merge ([ var ], []) existential_ctx )
               ~is_non_expansive
               ~bindings
               ~equations
               ~in_:(pat &~ exp)))
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
            let ((_, exp_type) as annotation) =
              Shallow_type.of_type annotation
            in
            let%bind exp = infer_exp exp exp_type in
            return
              Binding.(
                let_prec
                  ~universal_ctx:forall_vars
                  ~annotation
                  ~term_var:f
                  ~in_:exp))
          ~message:(fun var ->
            [%message
              "Duplicate variable in forall quantifier (let)" (var : string)])
      | `Unannotated (forall_vars, f, exp) ->
        extend_substitution_vars
          forall_vars
          ~f:(fun forall_vars ->
            let var = fresh () in
            let%bind exp = infer_exp exp var in
            return
              Binding.(
                let_mrec
                  ~ctx:(forall_vars, ([ var ], []))
                  ~binding:f #= var
                  ~in_:exp))
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
  let_
    ~bindings:
      Binding.
        [ let_
            ~ctx:([], ([], []))
            ~is_non_expansive:true
            ~equations:[]
            ~bindings:[]
            ~in_
        ]
    ~in_:(return ())
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
