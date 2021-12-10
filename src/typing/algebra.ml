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

module Term_var = struct
  type t = string [@@deriving sexp_of, compare]
end

module Type_var = struct
  type t = string [@@deriving sexp_of]

  let of_int x = "α" ^ Int.to_string x
end

module Type_former = struct
  type 'a t =
    | Arrow of 'a * 'a
    | Tuple of 'a list
    | Constr of 'a list * string
  [@@deriving sexp_of]

  let map t ~f =
    match t with
    | Arrow (t1, t2) ->
      let t1' = f t1 in
      let t2' = f t2 in
      Arrow (t1', t2')
    | Tuple ts -> Tuple (List.map ~f ts)
    | Constr (ts, constr) -> Constr (List.map ~f ts, constr)


  let iter t ~f = ignore (map t ~f)


  let fold t ~f ~init =
    match t with
    | Arrow (t1, t2) ->
      let init = f t1 init in
      let init = f t2 init in
      init
    | Tuple ts -> List.fold_right ~f ~init ts
    | Constr (ts, _) -> List.fold_right ~f ~init ts


  exception Iter2

  let iter2_exn t1 t2 ~f =
    let list_iter2 xs ys ~f =
      (* Catch the [Base] exception and re-raise our exception *)
      try List.iter2_exn xs ys ~f with
      | _ -> raise Iter2
    in
    match t1, t2 with
    | Arrow (t11, t12), Arrow (t21, t22) ->
      f t11 t21;
      f t12 t22
    | Tuple ts1, Tuple ts2 -> list_iter2 ts1 ts2 ~f
    | Constr (ts1, constr1), Constr (ts2, constr2)
      when String.equal constr1 constr2 -> list_iter2 ts1 ts2 ~f
    | _, _ -> raise Iter2
end

module Type = struct
  open Types

  type t = Types.type_expr [@@deriving sexp_of]

  let var x = Ttyp_var x

  let former former =
    match former with
    | Type_former.Arrow (t1, t2) -> Ttyp_arrow (t1, t2)
    | Type_former.Tuple ts -> Ttyp_tuple ts
    | Type_former.Constr (ts, constr) -> Ttyp_constr (ts, constr)

  let mu x t = Ttyp_alias (t, x)
end

module Algebra = struct
  module Term_var = Term_var

  module Types = struct
    module Var = Type_var
    module Former = Type_former
    module Type = Type

    type scheme = Var.t list * Type.t
  end
end