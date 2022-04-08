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
open Typedtree
open Constraint
open Predefined

let ( -~- ) type1 type2 : unit Constraint.t =
  let ctx1, var1 = Shallow_type.of_type type1 in
  let ctx2, var2 = Shallow_type.of_type type2 in
  Constraint.exists ~ctx:(Shallow_type.Ctx.merge ctx1 ctx2) (var1 =~ var2)


(** {1 : Environment helpers} *)

module Env = struct
  include Env

  module With_computation (Computation : Computation.S) = struct
    open Computation

    let substitution_of_vars vars =
      Substitution.of_alist (List.map ~f:(fun x -> x, fresh ()) vars)
      |> of_result ~message:(fun (`Duplicate_type_variable var) ->
             [%message "Duplicate type variable" (var : string)])


    let convert_type_expr ~substitution type_expr =
      let open Types in
      Convert.type_expr ~substitution type_expr
      |> of_result ~message:(function
             | `Unbound_type_variable var ->
               [%message
                 "Unbound type variable when converting type expression"
                   (var : string)]
             | `Type_expr_is_ill_sorted type_expr ->
               [%message
                 "Type expression is ill-sorted" (type_expr : type_expr)]
             | `Type_expr_contains_alias type_expr ->
               [%message
                 "Type expression contains alias" (type_expr : type_expr)])


    let find_constr constr_name =
      let open Let_syntax in
      let%bind env = env in
      (* Determine the constructor argument, type and alphas using
         the environment [env] and the constructor name [name]. *)
      let%bind { constructor_arg = constr_arg
               ; constructor_type = constr_type
               ; constructor_alphas = constr_alphas
               ; constructor_constraints = constr_constraints
               ; _
               }
        =
        Env.find_constr env constr_name
        |> of_result ~message:(fun `Unbound_constructor ->
               [%message
                 "Constructor is unbound in environment" (constr_name : string)])
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
              List.find
                ~f:(List.mem ~equal:String.equal constr_betas)
                constr_alphas
            with
            | Some var ->
              fail [%message "Duplicate type variable" (var : string)]
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
            return (type1, type2))
        |> all
      in
      return (alphas, constr_arg, constr_type, constr_constraints)


    let find_label label_name =
      let open Let_syntax in
      let%bind env = env in
      let%bind { label_arg; label_type; label_alphas; label_betas; _ } =
        Env.find_label env label_name
        |> of_result ~message:(fun `Unbound_label ->
               [%message
                 "Label is unbound in environment" (label_name : string)])
      in
      (* Redefined due to repeated error function *)
      let substitution_of_vars vars = substitution_of_vars vars in
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
  end
end

(** {2 : GADTs} *)

(* [is_constr_generalized ~enc constr] returns whether the constructor [constr] is a constructor of a GADT *)
let is_constr_generalized ~env constr =
  let open Result.Let_syntax in
  let%map { constructor_constraints; _ } = Env.find_constr env constr in
  not (List.is_empty constructor_constraints)


(* [is_pat_generalized ~env pat] returns whether the pattern [pat] contains a generalized constructor *)
let rec is_pat_generalized ~env pat =
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
let is_case_generalized ~env case = is_pat_generalized ~env case.pc_lhs

(* [is_case_generalized ~env cases] returns whether the cases contains a generalized case.
   Will be used later on! *)
let[@warning "-32"] is_cases_generalized ~env cases =
  let open Result.Let_syntax in
  let%map is_cases_generalized =
    List.map cases ~f:(is_case_generalized ~env) |> Result.all
  in
  List.exists ~f:Fn.id is_cases_generalized


(** {3: Polymorphic variants} *)

type variant_pattern = Vpat_variant of string * Parsetree.pattern option

let variant_pattern_of_pattern pat =
  match pat with
  | Ppat_variant (tag, arg_pat) -> Some (Vpat_variant (tag, arg_pat))
  | _ -> None


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

let variant_default_case_of_case { pc_lhs = pat; pc_rhs = exp } =
  match pat with
  | Ppat_any -> Some { vdc_lhs = Vpat_any; vdc_rhs = exp }
  | Ppat_var x -> Some { vdc_lhs = Vpat_var x; vdc_rhs = exp }
  | _ -> None


let variant_case_of_case { pc_lhs = pat; pc_rhs = exp } =
  match pat with
  | Ppat_variant (tag, pat) ->
    Some { vc_lhs = Vpat_variant (tag, pat); vc_rhs = exp }
  | _ -> None


let rec variant_cases_of_cases cases =
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


(** {4 : Helpers for constructing descriptors} *)

let make_constr_desc constr_name constr_arg constr_type =
  let open Types in
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


let make_label_desc label_name label_arg label_type =
  let open Types in
  let open Constraint.Let_syntax in
  let%map label_type = decode label_type
  and label_arg = decode label_arg in
  { label_name; label_type; label_arg }


let make_variant_desc variant_tag variant_row =
  let open Types in
  let open Constraint.Let_syntax in
  let%map variant_row = decode variant_row in
  { variant_tag; variant_row }


(** {5 : Value restriction} *)

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


(** {6 : Polymorphic recursion functions} *)

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


(** {7 : Inference} *)

let infer_constant const =
  let open Ast_types in
  match const with
  | Const_int _ -> int
  | Const_bool _ -> bool
  | Const_float _ -> float
  | Const_char _ -> char
  | Const_string _ -> string
  | Const_unit -> unit


module Pattern = struct
  module Computation = Computation.Pattern
  module Convert = Convert.With_computation (Computation)
  open Computation
  open Computation.Binder
  open Env.With_computation (Computation)

  let inst_constr constr_name constr_type' =
    let open Binder.Let_syntax in
    (* Lookup constructor in environment. *)
    let& alphas, constr_arg, constr_type, constr_constraints =
      find_constr constr_name
    in
    (* Bind [alphas] existentially. *)
    let%bind () = exists_vars alphas in
    (* Convert [constr_arg] and [constr_type] to variables *)
    let%bind constr_arg =
      match constr_arg with
      | Some (constr_betas, constr_arg) ->
        let%bind () = forall_ctx ~ctx:constr_betas in
        let%bind constr_arg = of_type constr_arg in
        return (Some (constr_betas, constr_arg))
      | None -> return None
    in
    let%bind constr_type = of_type constr_type in
    (* Build constraint. *)
    let constr_desc =
      constr_type
      =~ constr_type'
      >> make_constr_desc constr_name Option.(constr_arg >>| snd) constr_type
    in
    return (constr_desc, constr_arg, constr_constraints)


  let bind_constr_betas ~arg_betas ~constr_betas ~in_ =
    let open Computation.Let_syntax in
    if List.is_empty arg_betas
    then in_
    else (
      match List.zip arg_betas constr_betas with
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
        extend_substitution ~substitution in_
      | Unequal_lengths ->
        fail
          [%message
            "Constructor existential variable mistmatch with definition"])


  let infer_pat pat pat_type =
    let rec infer_pat pat pat_type =
      let open Computation.Let_syntax in
      let%bind pat_desc = infer_pat_desc pat pat_type in
      return
        (let%map pat_desc = pat_desc
         and pat_type = decode pat_type in
         { pat_desc; pat_type })
    and infer_pat_desc pat pat_type =
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
          (let%map () = pat_type =~= Former (Type_former.tuple vars)
           and pats = pats in
           Tpat_tuple pats)
      | Ppat_construct (constr, arg_pat) ->
        let@ constr_desc, arg_pat_type, constr_constraint =
          inst_constr constr pat_type
        in
        let%bind () = assert_ constr_constraint in
        let%bind arg_pat =
          match arg_pat, arg_pat_type with
          | Some (arg_betas, arg_pat), Some (constr_betas, arg_pat_type) ->
            bind_constr_betas
              ~arg_betas
              ~constr_betas
              ~in_:
                (let%bind pat = infer_pat arg_pat arg_pat_type in
                 return (constr_constraint #=> pat >>| Option.some))
          | None, None -> const None
          | _, _ ->
            fail
              [%message
                "Constructor argument mismatch in pattern"
                  (pat : Parsetree.pattern)]
        in
        return
          (let%map constr_desc = constr_desc
           and arg_pat = arg_pat in
           Tpat_construct (constr_desc, arg_pat))
      | Ppat_constraint (pat, pat_type') ->
        let%bind row_vars, pat_type' = Convert.core_type pat_type' in
        (* testing shows that row vars are existential in annotations *)
        let@ () = exists_vars row_vars in
        let@ pat_type1 = of_type pat_type' in
        let@ pat_type2 = of_type pat_type' in
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
    infer_pat pat pat_type


  let infer_variant_default_pat default_pat pat_type ~default_pat_type =
    let rec infer_pat pat pat_type =
      let open Computation.Let_syntax in
      let%bind pat_desc = infer_pat_desc pat in
      return
        (let%map pat_desc = pat_desc
         and pat_type = decode pat_type in
         { pat_desc; pat_type })
    and infer_pat_desc pat =
      let open Computation.Let_syntax in
      match pat with
      | Vpat_any -> const Tpat_any
      | Vpat_var x ->
        let%bind () = extend x default_pat_type in
        const (Tpat_var x)
    in
    infer_pat default_pat pat_type
end

module Expression = struct
  module Fragment = Computation.Fragment
  module Computation = Computation.Expression
  module Convert = Convert.With_computation (Computation)
  open Computation
  open Computation.Binder
  open Env.With_computation (Computation)

  let infer_pat pat pat_type =
    Pattern.(Computation.run (infer_pat pat pat_type))


  let infer_variant_default_pat default_pat pat_type ~default_pat_type =
    Pattern.(
      Computation.run
        (infer_variant_default_pat default_pat pat_type ~default_pat_type))


  let lift f shallow_type =
    let open Computation.Let_syntax in
    let var = fresh () in
    let%bind t = f var in
    return (Constraint.exists ~ctx:([ var ], [ var, shallow_type ]) t)


  let annotation_of_rec_value_binding value_binding =
    of_result (annotation_of_rec_value_binding value_binding) ~message:(function
        | `Invalid_recursive_binding ->
        [%message
          "Invalid recursive value binding form."
            (value_binding : Parsetree.value_binding)])


  let inst_constr constr_name constr_type' =
    let open Binder.Let_syntax in
    (* Lookup constructor in environment. *)
    let& constr_alphas, constr_arg, constr_type, constr_constraints =
      find_constr constr_name
    in
    (* Bind [alphas] existentially. *)
    let%bind () = exists_vars constr_alphas in
    (* Convert [constr_arg] and [constr_type] to variables *)
    let%bind constr_arg =
      match constr_arg with
      | Some (constr_betas, constr_arg) ->
        let%bind () = exists_vars constr_betas in
        let%bind constr_arg = of_type constr_arg in
        return (Some constr_arg)
      | None -> return None
    in
    let%bind constr_type = of_type constr_type in
    (* Build constraint. *)
    let constr_desc =
      constr_type
      =~ constr_type'
      >> Constraint.all_unit
           (List.map constr_constraints ~f:(fun (t1, t2) -> t1 -~- t2))
      >> make_constr_desc constr_name constr_arg constr_type
    in
    return (constr_desc, constr_arg)


  let inst_label label_name label_arg' label_type' =
    let open Computation.Let_syntax in
    let%bind label_alphas, label_betas, label_arg, label_type =
      find_label label_name
    in
    (* Bind [label_alphas] and [label_betas] existentially *)
    let@ () = exists_vars (label_alphas @ label_betas) in
    let label_desc =
      label_type'
      =~- label_type
      >> (label_arg' =~- label_arg)
      >> make_label_desc label_name label_arg' label_type'
    in
    return label_desc


  let inst_variant tag variant_row =
    let open Binder.Let_syntax in
    let%bind rho = exists () in
    let%bind tag_type = exists () in
    let variant_desc =
      variant_row
      =~- row_cons tag (present (Type.var tag_type)) (Type.var rho)
      >> make_variant_desc tag variant_row
    in
    return (variant_desc, tag_type)


  let bind_pat ~pat ~pat_type ~in_ =
    let open Computation.Let_syntax in
    let%bind fragment, pat = infer_pat pat pat_type in
    let universal_ctx, existential_ctx, equations, bindings, substitution =
      Fragment.to_bindings fragment
    in
    (* Bind [universal_ctx] universally, since it is bound both in [in_]
       and [pat]. *)
    let@ () = forall_ctx ~ctx:universal_ctx in
    let%bind in_ = extend_substitution ~substitution in_ in
    (* Construct a (pat, in_) pair using [let_1]  *)
    return
      (let%map (_, (_, pat)), in_ =
         let_1
           ~binding:
             Binding.(
               let_
                 ~ctx:([], existential_ctx)
                 ~is_non_expansive:true
                 ~bindings
                 ~in_:pat
                 ~equations)
           ~in_
       in
       pat, in_)


  let bind_variant_pat
      ~variant_pat:(Vpat_variant (tag, arg_pat))
      ~variant_pat_row
      ~in_
    =
    let open Binder.Let_syntax in
    (* Introduce new type for unknown type of [arg_pat] *)
    let%bind arg_pat_type = exists () in
    let%bind arg_pat_in_ =
      match arg_pat with
      | None ->
        (* [arg_pat_type = unit] if no pattern. *)
        let& in_ = in_ in
        return
          (let%map () = arg_pat_type =~- unit
           and in_ = in_ in
           None, in_)
      | Some arg_pat ->
        (* bind [arg_pat] with type [arg_pat_type] w/ [in_]. *)
        let& pat_in_ = bind_pat ~pat:arg_pat ~pat_type:arg_pat_type ~in_ in
        return
          (let%map pat, in_ = pat_in_ in
           Some pat, in_)
    in
    (* Pattern type is given by [Σ variant_pat_row]. *)
    let%bind pat_type = of_type (variant (Type.var variant_pat_row)) in
    return
      ( tag
      , arg_pat_type
      , let%map variant_desc = make_variant_desc tag variant_pat_row
        and arg_pat, in_ = arg_pat_in_
        and pat_type = decode pat_type in
        { pat_desc = Tpat_variant (variant_desc, arg_pat); pat_type }, in_ )


  let bind_variant_default_pat
      ~variant_default_pat
      ~default_pat_type
      ~pat_type
      ~in_
    =
    let open Computation.Let_syntax in
    (* Infer the pattern *)
    let%bind fragment, pat =
      infer_variant_default_pat variant_default_pat pat_type ~default_pat_type
    in
    (* Unpack the fragment; asserting that [universal_ctx] and [equations]
       are empty; since GADTs cannot occur in default patterns. *)
    let universal_ctx, existential_ctx, equations, bindings, _substitution =
      Fragment.to_bindings fragment
    in
    assert (List.is_empty universal_ctx);
    assert (List.is_empty equations);
    (* Bind [existential_ctx] existentially *)
    let@ () = exists_ctx ~ctx:existential_ctx in
    let%bind in_ = in_ in
    return
      (let%map pat = pat
       and in_ = def ~bindings ~in_ in
       pat, in_)


  let bind_forall ~vars ~on_duplicate_var ~in_ ~type_ =
    let open Computation.Let_syntax in
    extend_substitution_vars ~vars ~on_duplicate_var ~in_:(fun vars ->
        let internal_name = "@dromedary.internal.pexp_forall" in
        let var = fresh () in
        let%bind in_ = in_ var in
        return
          (let%map (_, (_, exp)), _ =
             let_1
               ~binding:
                 Binding.(
                   let_
                     ~ctx:(vars, ([ var ], []))
                     ~is_non_expansive:true
                     ~bindings:[ internal_name #= var ]
                     ~in_
                     ~equations:[])
               ~in_:(inst internal_name type_)
           in
           exp))


  let bind_exists ~vars ~on_duplicate_var ~in_ ~type_ =
    let open Computation.Let_syntax in
    extend_substitution_vars ~vars ~on_duplicate_var ~in_:(fun vars ->
        let@ () = exists_vars vars in
        in_ type_)


  let infer_primitive prim : Type.t Binder.t =
    let open Ast_types in
    let open Binder.Let_syntax in
    match prim with
    | Prim_add | Prim_sub | Prim_div | Prim_mul -> return (int @-> int @-> int)
    | Prim_eq -> return (int @-> int @-> bool)
    | Prim_ref ->
      let%bind var = exists () in
      let var = Type.var var in
      return (var @-> ref var)
    | Prim_deref ->
      let%bind var = exists () in
      let var = Type.var var in
      return (ref var @-> var)
    | Prim_assign ->
      let%bind var = exists () in
      let var = Type.var var in
      return (ref var @-> var @-> unit)


  let rec infer_exp exp exp_type =
    let open Computation.Let_syntax in
    let%bind exp_desc = infer_exp_desc exp exp_type in
    return
      (let%map exp_desc = exp_desc
       and exp_type = decode exp_type in
       { exp_desc; exp_type })


  and infer_exp_desc exp exp_type =
    let open Computation.Let_syntax in
    match exp with
    | Pexp_var x ->
      return
        (let%map instances = inst x exp_type in
         Texp_var (x, instances))
    | Pexp_prim prim ->
      let@ prim_type = infer_primitive prim in
      return
        (let%map () = exp_type =~- prim_type in
         Texp_prim prim)
    | Pexp_const const ->
      let const_type = infer_constant const in
      return
        (let%map () = exp_type =~- const_type in
         Texp_const const)
    | Pexp_fun (pat, exp) ->
      let@ var1 = exists () in
      let@ var2 = exists () in
      let%bind pat_exp =
        bind_pat ~pat ~pat_type:var1 ~in_:(infer_exp exp var2)
      in
      return
        (let%map () = exp_type =~= Former Type_former.(var1 @-> var2)
         and pat, exp = pat_exp in
         Texp_fun (pat, exp))
    | Pexp_app (exp1, exp2) ->
      let@ var = exists () in
      let%bind exp1 =
        lift (infer_exp exp1) (Former Type_former.(var @-> exp_type))
      in
      let%bind exp2 = infer_exp exp2 var in
      return
        (let%map exp1 = exp1
         and exp2 = exp2 in
         Texp_app (exp1, exp2))
    | Pexp_constraint (Pexp_match (match_exp, cases), exp_type') ->
      let annotate_case case =
        { case with pc_rhs = Pexp_constraint (case.pc_rhs, exp_type') }
      in
      let%bind row_vars, exp_type' = Convert.core_type exp_type' in
      let@ () = exists_vars row_vars in
      let@ exp_type1 = of_type exp_type' in
      let@ exp_type2 = of_type exp_type' in
      let%bind exp_desc =
        infer_exp_desc
          (Pexp_match (match_exp, List.map ~f:annotate_case cases))
          exp_type1
      in
      return
        (let%map () = exp_type =~ exp_type2
         and exp_desc = exp_desc in
         exp_desc)
    | Pexp_constraint (exp, exp_type') ->
      let%bind row_vars, exp_type' = Convert.core_type exp_type' in
      let@ () = exists_vars row_vars in
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
        (let%map () = exp_type =~= Former (Type_former.tuple vars)
         and exps = exps in
         Texp_tuple exps)
    | Pexp_match (match_exp, cases) ->
      let@ var = exists () in
      let%bind match_exp = infer_exp match_exp var in
      let%bind cases = infer_cases cases ~lhs_type:var ~rhs_type:exp_type in
      return
        (let%map match_exp = match_exp
         and match_exp_type = decode var
         and cases = cases in
         Texp_match (match_exp, match_exp_type, cases))
    | Pexp_ifthenelse (if_exp, then_exp, else_exp) ->
      let%bind if_exp = lift (infer_exp if_exp) (Former Type_former.bool) in
      let%bind then_exp = infer_exp then_exp exp_type in
      let%bind else_exp = infer_exp else_exp exp_type in
      return
        (let%map if_exp = if_exp
         and then_exp = then_exp
         and else_exp = else_exp in
         Texp_ifthenelse (if_exp, then_exp, else_exp))
    | Pexp_exists (vars, exp) ->
      bind_exists
        ~vars
        ~on_duplicate_var:(fun var ->
          [%message
            "Duplicate variable in existential quantifier (exists)"
              (exp : Parsetree.expression)
              (var : string)])
        ~in_:(infer_exp_desc exp)
        ~type_:exp_type
    | Pexp_forall (vars, exp) ->
      bind_forall
        ~vars
        ~on_duplicate_var:(fun var ->
          [%message
            "Duplicate variable in universal quantifier (forall)"
              (exp : Parsetree.expression)
              (var : string)])
        ~in_:(infer_exp_desc exp)
        ~type_:exp_type
    | Pexp_field (exp, label) ->
      let@ var = exists () in
      let%bind exp = infer_exp exp var in
      let%bind label_desc = inst_label label exp_type var in
      return
        (let%map exp = exp
         and label_desc = label_desc in
         Texp_field (exp, label_desc))
    | Pexp_record label_defs ->
      let%bind label_exps = infer_label_defs label_defs exp_type in
      return
        (let%map label_exps = label_exps in
         Texp_record label_exps)
    | Pexp_construct (constr, arg_exp) ->
      let@ constr_desc, arg_exp_type = inst_constr constr exp_type in
      let%bind arg_exp =
        match arg_exp, arg_exp_type with
        | Some arg_exp, Some arg_exp_type ->
          let%bind exp = infer_exp arg_exp arg_exp_type in
          return (exp >>| Option.some)
        | None, None -> const None
        | _, _ ->
          fail
            [%message
              "Constructor argument mismatch in expression"
                (exp : Parsetree.expression)]
      in
      return
        (let%map constr_desc = constr_desc
         and arg_exp = arg_exp in
         Texp_construct (constr_desc, arg_exp))
    | Pexp_variant (tag, arg_exp) ->
      let@ row = exists () in
      let@ variant_desc, arg_exp_type = inst_variant tag row in
      let%bind arg_exp =
        match arg_exp with
        | Some arg_exp ->
          let%bind exp = infer_exp arg_exp arg_exp_type in
          return (exp >>| Option.some)
        | None ->
          return
            (let%map () = arg_exp_type =~- unit in
             None)
      in
      return
        (let%map variant_desc = variant_desc
         and arg_exp = arg_exp
         and () = exp_type =~- variant (Type.var row) in
         Texp_variant (variant_desc, arg_exp))
    | Pexp_try (exp, cases) ->
      let%bind exp = infer_exp exp exp_type in
      let@ exn = of_type exn in
      let%bind cases = infer_cases cases ~lhs_type:exn ~rhs_type:exp_type in
      return
        (let%map exp = exp
         and cases = cases in
         Texp_try (exp, cases))
    | Pexp_sequence (exp1, exp2) ->
      let%bind exp1 = lift (infer_exp exp1) (Former Type_former.unit) in
      let%bind exp2 = infer_exp exp2 exp_type in
      return
        (let%map exp1 = exp1
         and exp2 = exp2 in
         Texp_sequence (exp1, exp2))
    | Pexp_while (exp1, exp2) ->
      let%bind exp1 = lift (infer_exp exp1) (Former Type_former.bool) in
      let%bind exp2 = lift (infer_exp exp2) (Former Type_former.unit) in
      return
        (let%map () = exp_type =~= Former Type_former.unit
         and exp1 = exp1
         and exp2 = exp2 in
         Texp_while (exp1, exp2))
    | Pexp_for (pat, exp1, exp2, direction_flag, exp3) ->
      let%bind index =
        match pat with
        | Ppat_any -> return "@dromedary.internal.pexp_for.for"
        | Ppat_var x -> return x
        | _ ->
          fail [%message "Invalid for loop index" (pat : Parsetree.pattern)]
      in
      let%bind exp1 = lift (infer_exp exp1) (Former Type_former.int) in
      let%bind exp2 = lift (infer_exp exp2) (Former Type_former.int) in
      let%bind exp3 = lift (infer_exp exp3) (Former Type_former.unit) in
      let@ int = of_type int in
      return
        (let%map () = exp_type =~= Former Type_former.unit
         and exp1 = exp1
         and exp2 = exp2
         and exp3 = def ~bindings:[ index #= int ] ~in_:exp3 in
         Texp_for (index, exp1, exp2, direction_flag, exp3))
    | Pexp_let (Nonrecursive, value_bindings, exp) ->
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
        (let%map let_bindings, exp = let_rec ~bindings:let_bindings ~in_:exp in
         Texp_let_rec (List.map ~f:to_rec_value_binding let_bindings, exp))


  and infer_exps exps =
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


  and infer_cases cases ~lhs_type ~rhs_type =
    let open Computation.Let_syntax in
    match variant_cases_of_cases cases with
    | None ->
      let%bind cases =
        cases |> List.map ~f:(infer_case ~lhs_type ~rhs_type) |> Computation.all
      in
      return (Constraint.all cases)
    | Some variant_cases ->
      infer_variant_cases variant_cases ~lhs_type ~rhs_type


  and infer_variant_cases { cases; default_case } ~lhs_type ~rhs_type =
    let open Computation.Let_syntax in
    (* Create [lhs_row]; row variable for the match cases *)
    let@ lhs_row = exists () in
    (* Create [default_pat_type]; may be unified to [∂absent] if match is closed *)
    let@ default_pat_type = exists () in
    let@ cases =
      cases |> List.map ~f:(infer_variant_case ~lhs_row ~rhs_type) |> Binder.all
    in
    let%bind default_case =
      match default_case with
      | None ->
        return
          (let%map () = default_pat_type =~- row_uniform absent in
           None)
      | Some default_case ->
        let%bind default_case =
          infer_variant_default_case
            default_case
            ~lhs_type
            ~rhs_type
            ~default_pat_type
        in
        return
          (let%map default_case = default_case in
           Some default_case)
    in
    let row, cases =
      List.fold_right
        cases
        ~init:(Type.var default_pat_type, [])
        ~f:(fun (tag, var, case) (row, cases) ->
          row_cons tag (Type.var var) row, case :: cases)
    in
    return
      (let%map () = lhs_type =~- variant row
       and () = lhs_row =~- row
       and cases = Constraint.all cases
       and default_case = default_case in
       match default_case with
       | None -> cases
       | Some default_case -> cases @ [ default_case ])


  and infer_case { pc_lhs = pat; pc_rhs = exp } ~lhs_type ~rhs_type
      : Typedtree.case Constraint.t Computation.t
    =
    let open Computation.Let_syntax in
    let%bind pat_exp =
      bind_pat ~pat ~pat_type:lhs_type ~in_:(infer_exp exp rhs_type)
    in
    return
      (let%map pat, exp = pat_exp in
       { tc_lhs = pat; tc_rhs = exp })


  and infer_variant_default_case
      { vdc_lhs; vdc_rhs }
      ~lhs_type
      ~rhs_type
      ~default_pat_type
    =
    let open Computation.Let_syntax in
    let%bind pat_exp =
      bind_variant_default_pat
        ~variant_default_pat:vdc_lhs
        ~pat_type:lhs_type
        ~default_pat_type
        ~in_:(infer_exp vdc_rhs rhs_type)
    in
    return
      (let%map pat, exp = pat_exp in
       { tc_lhs = pat; tc_rhs = exp })


  and infer_variant_case { vc_lhs; vc_rhs } ~lhs_row ~rhs_type =
    let open Binder.Let_syntax in
    let%bind tag, tag_type, pat_exp =
      bind_variant_pat
        ~variant_pat:vc_lhs
        ~variant_pat_row:lhs_row
        ~in_:(infer_exp vc_rhs rhs_type)
    in
    return
      ( tag
      , tag_type
      , let%map pat, exp = pat_exp in
        { tc_lhs = pat; tc_rhs = exp } )


  and infer_label_defs label_defs record_type =
    let open Computation.Let_syntax in
    let%bind label_defs =
      label_defs
      |> List.map ~f:(fun (label, exp) -> infer_label_def label exp record_type)
      |> Computation.all
    in
    return (Constraint.all label_defs)


  and infer_label_def label exp label_type' =
    let open Computation.Let_syntax in
    let%bind label_alphas, label_betas, label_arg, label_type =
      find_label label
    in
    (* Bind [label_alphas] existentially *)
    let@ () = exists_vars label_alphas in
    (* Bind [label_betas] universally *)
    let@ () = forall_ctx ~ctx:label_betas in
    (* Convert [label_arg] and [label_type] to variables *)
    let@ label_arg = of_type label_arg in
    let@ label_type = of_type label_type in
    (* [exp] has the type [label_arg] *)
    let%bind exp = infer_exp exp label_arg in
    (* Make label descriptor *)
    let label_desc =
      label_type' =~ label_type >> make_label_desc label label_arg label_type
    in
    return (label_desc &~ exp)


  and infer_value_bindings value_bindings =
    value_bindings |> List.map ~f:infer_value_binding |> Computation.all


  and infer_value_binding
      { pvb_forall_vars = forall_vars; pvb_pat = pat; pvb_expr = exp }
    =
    let open Computation.Let_syntax in
    extend_substitution_vars
      ~vars:forall_vars
      ~on_duplicate_var:(fun var ->
        [%message
          "Duplicate variable in universal quantifier (let)"
            (exp : Parsetree.expression)
            (var : string)])
      ~in_:(fun forall_vars ->
        (* [var] is the type of the binding *)
        let var = fresh () in
        (* [pat] has the type var *)
        let%bind fragment, pat = infer_pat pat var in
        let universal_ctx, existential_ctx, equations, bindings, _substitution =
          Fragment.to_bindings fragment
        in
        (* Do not introduce existential vars using let-bindings *)
        assert (List.is_empty universal_ctx);
        (* [exp] has the type var *)
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


  and infer_rec_value_bindings rec_value_bindings =
    rec_value_bindings |> List.map ~f:infer_rec_value_binding |> Computation.all


  and infer_rec_value_binding value_binding =
    let open Computation.Let_syntax in
    match%bind annotation_of_rec_value_binding value_binding with
    | `Annotated (forall_vars, f, exp, annotation) ->
      extend_substitution_vars
        ~vars:forall_vars
        ~on_duplicate_var:(fun var ->
          [%message
            "Duplicate variable in forall quantifier (let)" (var : string)])
        ~in_:(fun forall_vars ->
          (* Convert [annotation] to shallow type *)
          let%bind row_vars, annotation = Convert.core_type annotation in
          let ((_, exp_type) as annotation) = Shallow_type.of_type annotation in
          (* [exp] has the annotated type [exp_type] *)
          let%bind exp = infer_exp exp exp_type in
          return
            Binding.(
              let_prec
                ~universal_ctx:(row_vars @ forall_vars)
                ~annotation
                ~term_var:f
                ~in_:exp))
    | `Unannotated (forall_vars, f, exp) ->
      extend_substitution_vars
        ~vars:forall_vars
        ~on_duplicate_var:(fun var ->
          [%message
            "Duplicate variable in forall quantifier (let)" (var : string)])
        ~in_:(fun forall_vars ->
          (* [var] is the type of the binding *)
          let var = fresh () in
          (* [exp] has the type [var] *)
          let%bind exp = infer_exp exp var in
          return
            Binding.(
              let_mrec
                ~ctx:(forall_vars, ([ var ], []))
                ~binding:f #= var
                ~in_:exp))


  let infer_exp_ exp =
    let open Computation.Let_syntax in
    let%bind exp =
      let@ var = exists () in
      infer_exp exp var
    in
    return (let_0 ~in_:exp)


  module Structure = struct
    open Structure.Item

    let infer_value_binding
        { pvb_forall_vars = forall_vars; pvb_pat = pat; pvb_expr = exp }
      =
      let open Computation.Let_syntax in
      extend_substitution_vars
        ~vars:forall_vars
        ~on_duplicate_var:(fun var ->
          [%message
            "Duplicate variable in universal quantifier (let)"
              (exp : Parsetree.expression)
              (var : string)])
        ~in_:(fun forall_vars ->
          (* [var] is the type of the binding *)
          let var = fresh () in
          (* [pat] has the type var *)
          let%bind fragment, pat = infer_pat pat var in
          let ( universal_ctx
              , existential_ctx
              , _equations
              , bindings
              , _substitution )
            =
            Fragment.to_bindings fragment
          in
          (* Do not introduce existential vars using let-bindings *)
          assert (List.is_empty universal_ctx);
          (* [exp] has the type var *)
          let is_non_expansive = is_non_expansive exp in
          let%bind exp = infer_exp exp var in
          return
            (Binding.let_
               ~ctx:
                 ( forall_vars
                 , Shallow_type.Ctx.merge ([ var ], []) existential_ctx )
               ~is_non_expansive
               ~bindings
               ~in_:(pat &~ exp)))


    let infer_value_bindings value_bindings =
      value_bindings |> List.map ~f:infer_value_binding |> Computation.all


    let infer_rec_value_bindings = infer_rec_value_bindings
  end
end
