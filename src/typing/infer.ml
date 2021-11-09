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

open Base
open Constraints.Intf

(* ------------------------------------------------------------------------- *)

(* Implement required interfaces from [Constraints.Intf]. *)

module Term_var = struct
  type t = string [@@deriving sexp_of, compare]
end

module Type_var = struct
  type t = string [@@deriving sexp_of]

  let of_int x = "α" ^ Int.to_string x
end

module Type_former = struct
  type 'a t =
    | Ttyp_form_arrow of 'a * 'a
    | Ttyp_form_tuple of 'a list
    | Ttyp_form_constr of 'a list * string
  [@@deriving sexp_of]

  let map t ~f =
    match t with
    | Ttyp_form_arrow (t1, t2) ->
      let t1' = f t1 in
      let t2' = f t2 in
      Ttyp_form_arrow (t1', t2')
    | Ttyp_form_tuple ts -> Ttyp_form_tuple (List.map ~f ts)
    | Ttyp_form_constr (ts, constr) -> Ttyp_form_constr (List.map ~f ts, constr)


  let iter t ~f =
    let (_ : unit t) = map t ~f in
    ()


  let fold t ~f ~init =
    match t with
    | Ttyp_form_arrow (t1, t2) ->
      let init = f t1 init in
      let init = f t2 init in
      init
    | Ttyp_form_tuple ts -> List.fold_right ~f ~init ts
    | Ttyp_form_constr (ts, _) -> List.fold_right ~f ~init ts


  exception Iter2

  let iter2 t1 t2 ~f =
    let list_iter2 xs ys ~f =
      (* Catch the [Base] exception and re-raise our exception *)
      try List.iter2_exn xs ys ~f with
      | _ -> raise Iter2
    in
    match t1, t2 with
    | Ttyp_form_arrow (t11, t12), Ttyp_form_arrow (t21, t22) ->
      f t11 t21;
      f t12 t22
    | Ttyp_form_tuple ts1, Ttyp_form_tuple ts2 -> list_iter2 ts1 ts2 ~f
    | Ttyp_form_constr (ts1, constr1), Ttyp_form_constr (ts2, constr2)
      when String.equal constr1 constr2 -> list_iter2 ts1 ts2 ~f
    | _, _ -> raise Iter2
end

module Type = struct
  type var = Type_var.t
  type 'a former = 'a Type_former.t
  type t = Types.type_expr [@@deriving sexp_of]

  open Types

  let var x = Ttyp_var x

  let form former =
    let open Type_former in
    match former with
    | Ttyp_form_arrow (t1, t2) -> Ttyp_arrow (t1, t2)
    | Ttyp_form_tuple ts -> Ttyp_tuple ts
    | Ttyp_form_constr (ts, constr) -> Ttyp_constr (ts, constr)
end

module Types = struct

  module Var = Type_var

  module Former = Type_former

  module Type = Type

  type scheme = Var.t list * Type.t

end

(* ------------------------------------------------------------------------- *)
