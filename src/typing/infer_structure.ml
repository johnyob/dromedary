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
open Types
open Parsetree
open Typedtree
open Constraint
open Constraint.Structure

module Predefined = struct
  let absent = Type_expr.make (Ttyp_constr ([], "absent"))
  let present x = Type_expr.make (Ttyp_constr ([ x ], "present"))
  let row_cons tag t1 t2 = Type_expr.make (Ttyp_row_cons (tag, t1, t2))
  let row_uniform t = Type_expr.make (Ttyp_row_uniform t)
  let unit = Type_expr.make (Ttyp_constr ([], "unit"))
end

let rec transl_core_type ~substitution core_type =
  let open Types in
  match core_type with
  | Ptyp_var x -> [], Map.find_exn substitution x
  | Ptyp_arrow (core_type1, core_type2) ->
    let vars1, t1 = transl_core_type ~substitution core_type1 in
    let vars2, t2 = transl_core_type ~substitution core_type2 in
    vars1 @ vars2, Type_expr.make (Ttyp_arrow (t1, t2))
  | Ptyp_tuple core_types ->
    let vars, ts =
      List.map core_types ~f:(transl_core_type ~substitution) |> List.unzip
    in
    List.concat vars, Type_expr.make (Ttyp_tuple ts)
  | Ptyp_constr (core_types, constr_name) ->
    let vars, ts =
      List.map core_types ~f:(transl_core_type ~substitution) |> List.unzip
    in
    List.concat vars, Type_expr.make (Ttyp_constr (ts, constr_name))
  | Ptyp_variant row ->
    let vars, t = transl_row ~substitution row in
    vars, Type_expr.make (Ttyp_variant t)
  | Ptyp_mu (var, core_type) ->
    let var' = Type_var.make () in
    let substitution =
      Map.set substitution ~key:var ~data:(Type_expr.make (Ttyp_var var'))
    in
    let vars, t = transl_core_type ~substitution core_type in
    vars, Type_expr.mu var' t
  | Ptyp_where (core_type1, var, core_type2) ->
    let vars2, t2 = transl_core_type ~substitution core_type2 in
    let substitution = Map.set substitution ~key:var ~data:t2 in
    let vars1, t1 = transl_core_type ~substitution core_type1 in
    vars1 @ vars2, t1


and transl_row ~substitution (row_fields, closed_flag) =
  let vars, tl =
    match closed_flag with
    | Closed -> [], Predefined.(row_uniform absent)
    | Open ->
      let var = Type_var.make () in
      [ var ], Type_expr.make (Ttyp_var var)
  in
  List.fold_right row_fields ~init:(vars, tl) ~f:(fun rf (vars1, tl) ->
    let vars2, row = transl_row_field ~substitution rf tl in
    vars1 @ vars2, row)


and transl_row_field ~substitution (Row_tag (tag, t)) tl =
  let vars, t =
    match t with
    | None -> [], Predefined.(present unit)
    | Some t ->
      let vars, t = transl_core_type ~substitution t in
      vars, Predefined.present t
  in
  vars, Predefined.row_cons tag t tl


let transl_constr_arg ~substitution constr_arg =
  let open Types in
  match constr_arg with
  | None -> substitution, None
  | Some constr_arg ->
    let { pconstructor_arg_betas = constr_arg_betas
        ; pconstructor_arg_type = constr_arg_type
        }
      =
      constr_arg
    in
    let substitution, constr_arg_betas =
      List.fold_left
        ~init:(substitution, [])
        ~f:(fun (substitution, betas) beta ->
          let var = Type_var.make () in
          ( Map.set substitution ~key:beta ~data:(Type_expr.make (Ttyp_var var))
          , var :: betas ))
        constr_arg_betas
    in
    let row_vars, type_expr = transl_core_type ~substitution constr_arg_type in
    ( substitution
    , Some
        { constructor_arg_betas = row_vars @ constr_arg_betas
        ; constructor_arg_type = type_expr
        } )


let transl_type_constr type_params type_name =
  Type_expr.make
    (Ttyp_constr
       ( List.map type_params ~f:(fun var -> Type_expr.make (Ttyp_var var))
       , type_name ))


let transl_constraint ~substitution =
  let transl_core_type core_type =
    let row_vars, t = transl_core_type ~substitution core_type in
    if not (List.is_empty row_vars)
    then
      raise_s [%message "Open polymorphic variant equations are not supported!"];
    t
  in
  fun (core_type1, core_type2) ->
    transl_core_type core_type1, transl_core_type core_type2


let transl_constr_decl constr_decl ~substitution ~type_params ~type_name =
  let open Types in
  let { pconstructor_name = constr_name
      ; pconstructor_arg = constr_arg
      ; pconstructor_constraints = constr_constraints
      }
    =
    constr_decl
  in
  let substitution, constr_arg = transl_constr_arg ~substitution constr_arg in
  let constr_type = transl_type_constr type_params type_name in
  { constructor_name = constr_name
  ; constructor_alphas = type_params
  ; constructor_arg = constr_arg
  ; constructor_type = constr_type
  ; constructor_constraints =
      List.map constr_constraints ~f:(transl_constraint ~substitution)
  }


let transl_label_decl label_decl ~substitution ~type_params ~type_name =
  let open Types in
  let { plabel_name = label_name
      ; plabel_betas = label_betas
      ; plabel_arg = label_arg
      }
    =
    label_decl
  in
  let substitution, label_betas =
    List.fold_left
      ~init:(substitution, [])
      ~f:(fun (substitution, betas) beta ->
        let var = Type_var.make () in
        ( Map.set substitution ~key:beta ~data:(Type_expr.make (Ttyp_var var))
        , var :: betas ))
      label_betas
  in
  let row_vars, label_arg = transl_core_type ~substitution label_arg in
  let label_type = transl_type_constr type_params type_name in
  { label_name
  ; label_alphas = type_params
  ; label_betas = row_vars @ label_betas
  ; label_arg
  ; label_type
  }


let transl_alias alias_type ~substitution ~type_params ~type_name =
  let open Types in
  let row_vars, alias_type = transl_core_type ~substitution alias_type in
  if not (List.is_empty row_vars)
  then raise_s [%message "Open polymorphic variant aliases not supported!"];
  { alias_alphas = type_params; alias_name = type_name; alias_type }


let transl_type_decl type_decl =
  let open Types in
  let { ptype_name = type_name; ptype_params = type_params; ptype_kind } =
    type_decl
  in
  let type_vars = List.map ~f:(fun _ -> Type_var.make ()) type_params in
  let substitution =
    String.Map.of_alist_exn
      (List.zip_exn
         type_params
         (List.map ~f:(fun var -> Type_expr.make (Ttyp_var var)) type_vars))
  in
  let type_kind =
    match ptype_kind with
    | Ptype_variant constr_decls ->
      Type_variant
        (List.map
           constr_decls
           ~f:
             (transl_constr_decl
                ~substitution
                ~type_params:type_vars
                ~type_name))
    | Ptype_record label_decls ->
      Type_record
        (List.map
           label_decls
           ~f:
             (transl_label_decl ~substitution ~type_params:type_vars ~type_name))
    | Ptype_abstract -> Type_abstract
    | Ptype_alias alias_type ->
      Type_alias
        (transl_alias
           alias_type
           ~substitution
           ~type_params:type_vars
           ~type_name)
    | Ptype_open -> Type_open
  in
  { type_name; type_kind }


let transl_ext_constr ext_constr ~substitution ~type_params ~type_name =
  let { pext_kind = Pext_decl constr_decl } = ext_constr in
  let constr_decl =
    transl_constr_decl constr_decl ~substitution ~type_params ~type_name
  in
  { text_name = type_name
  ; text_params = type_params
  ; text_kind = Text_decl constr_decl
  }


let transl_type_ext type_ext =
  let { ptyext_name; ptyext_params; ptyext_constructors = ptyext_constrs } =
    type_ext
  in
  let type_vars = List.map ~f:(fun _ -> Type_var.make ()) ptyext_params in
  let substitution =
    String.Map.of_alist_exn
      (List.zip_exn
         ptyext_params
         (List.map ~f:(fun var -> Type_expr.make (Ttyp_var var)) type_vars))
  in
  let tyext_constrs =
    List.map
      ptyext_constrs
      ~f:
        (transl_ext_constr
           ~substitution
           ~type_params:type_vars
           ~type_name:ptyext_name)
  in
  { tyext_name = ptyext_name; tyext_constructors = tyext_constrs }


let transl_type_exn type_exn =
  let { ptyexn_constructor } = type_exn in
  let tyexn_constructor =
    transl_ext_constr
      ptyexn_constructor
      ~substitution:String.Map.empty
      ~type_params:[]
      ~type_name:"exn"
  in
  { tyexn_constructor }


let convert_core_scheme (vars, core_type) =
  let open Result in
  let open Let_syntax in
  let%bind substitution =
    Substitution.of_alist (List.map vars ~f:(fun x -> x, fresh ()))
    |> map_error ~f:(fun (`Duplicate_type_variable var) ->
      [%message "Duplicate type variable" (var : string)])
  in
  let%bind vars, core_type =
    Convert.core_type ~substitution core_type
    |> map_error ~f:(fun (`Unbound_type_variable var) ->
      [%message
        "Unbound type variable when converting core type" (var : string)])
  in
  return (vars @ Substitution.rng substitution, core_type)


let infer_primitive { pval_name; pval_type; pval_prim } =
  let open Result.Let_syntax in
  let%bind vars, core_type = convert_core_scheme pval_type in
  let ctx, var = Shallow_type.of_type core_type in
  let ctx = [], Shallow_type.Ctx.merge (vars, []) ctx in
  return
    (let open Item in
     let%map.Item vars, type_ =
       let_1
         ~binding:
           Binding.(
             let_
               ~ctx
               ~is_non_expansive:true
               ~bindings:[ pval_name #= var ]
               ~in_:(Constraint.return ()))
       >>| function
       | [ (_, scheme) ], _ -> scheme
       | _ -> assert false
     in
     { tval_name = pval_name
     ; tval_type = List.map ~f:Type_var.decode vars, Type_expr.decode type_
     ; tval_prim = pval_prim
     })


let infer_exception ~env type_exn =
  let type_exn = transl_type_exn type_exn in
  let env = Env.add_ext_constr env type_exn.tyexn_constructor in
  env, type_exn


let infer_type_decl ~env type_decls =
  let type_decls = List.map type_decls ~f:transl_type_decl in
  let env =
    List.fold_right type_decls ~init:env ~f:(fun type_decl env ->
      Env.add_type_decl env type_decl)
  in
  env, type_decls


let infer_type_ext ~env type_ext =
  let type_ext = transl_type_ext type_ext in
  let env = Env.add_type_ext env type_ext in
  env, type_ext


let infer_rec_value_bindings ~env value_bindings =
  Infer_core.Expression.(
    Structure.infer_rec_value_bindings value_bindings |> Computation.run ~env)


let infer_value_bindings ~env value_bindings =
  Infer_core.Expression.(
    Structure.infer_value_bindings value_bindings |> Computation.run ~env)


let infer_str_item ~env str_item =
  let open Result.Let_syntax in
  match str_item with
  | Pstr_primitive primitive ->
    let%bind primitive = infer_primitive primitive in
    return
      ( env
      , let%map.Item primitive = primitive in
        Tstr_primitive primitive )
  | Pstr_type type_decls ->
    let env, type_decls = infer_type_decl ~env type_decls in
    return (env, Item.return (Tstr_type type_decls))
  | Pstr_exception type_exn ->
    let env, type_exn = infer_exception ~env type_exn in
    return (env, Item.return (Tstr_exception type_exn))
  | Pstr_value (Recursive, rec_value_bindings) ->
    let%bind let_bindings = infer_rec_value_bindings ~env rec_value_bindings in
    let to_rec_value_binding ((var, (variables, _)), (_, exp)) =
      { trvb_var = var; trvb_expr = List.map ~f:Type_var.decode variables, exp }
    in
    return
      ( env
      , let%map.Item let_bindings = Item.let_rec ~bindings:let_bindings in
        Tstr_value_rec (List.map ~f:to_rec_value_binding let_bindings) )
  | Pstr_value (Nonrecursive, value_bindings) ->
    let%bind let_bindings = infer_value_bindings ~env value_bindings in
    let to_value_binding (_, (variables, (pat, exp))) =
      { tvb_pat = pat; tvb_expr = List.map ~f:Type_var.decode variables, exp }
    in
    return
      ( env
      , let%map.Item let_bindings = Item.let_ ~bindings:let_bindings in
        Tstr_value (List.map ~f:to_value_binding let_bindings) )
  | Pstr_typext type_ext ->
    let env, type_ext = infer_type_ext ~env type_ext in
    return (env, Item.return (Tstr_typext type_ext))


let rec infer_str ~env str =
  let open Result.Let_syntax in
  match str with
  | [] -> return (env, [])
  | str_item :: str ->
    let%bind env, str_item = infer_str_item ~env str_item in
    let%bind env, str = infer_str ~env str in
    return (env, str_item :: str)
