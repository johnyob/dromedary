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
open Core


module Algebra = struct
  open Constraints.Module_types

  module Term_var = struct
    type t = string [@@deriving sexp_of, compare]
  end

  module Type_var = struct
    type t = string [@@deriving sexp_of]

    let of_int x = "a" ^ Int.to_string x
  end

  module Type_former = struct
    module T = struct
      type 'a t =
        | Arrow of 'a * 'a
        | Tuple of 'a list
        | Constr of 'a list * string
        | Variant of 'a
      [@@deriving sexp_of]

      let id t =
        match t with
        | Arrow _ -> 0
        | Tuple _ -> 1
        | Variant _ -> 2
        | Constr (_, constr) -> 3 + String.hash constr


      module Traverse (F : Applicative.S) = struct
        module Intf = struct
          module type S = sig end
        end

        module F = struct
          include F
          include Applicative.Make_let_syntax (F) (Intf) ()
        end

        open F

        let traverse t ~f =
          let open Let_syntax in
          match t with
          | Arrow (t1, t2) ->
            let%map t1 = f t1
            and t2 = f t2 in
            Arrow (t1, t2)
          | Tuple ts ->
            let%map ts = all (List.map ~f ts) in
            Tuple ts
          | Constr (ts, constr) ->
            let%map ts = all (List.map ~f ts) in
            Constr (ts, constr)
          | Variant t ->
            let%map t = f t in
            Variant t


        let traverse2 t1 t2 ~f =
          let open Let_syntax in
          let open List.Or_unequal_lengths in
          match t1, t2 with
          | Arrow (t11, t12), Arrow (t21, t22) ->
            `Ok
              (let%map t1 = f t11 t21
               and t2 = f t12 t22 in
               Arrow (t1, t2))
          | Tuple ts1, Tuple ts2 ->
            (match List.map2 ~f ts1 ts2 with
            | Ok ts ->
              `Ok
                (let%map ts = all ts in
                 Tuple ts)
            | Unequal_lengths -> `Unequal_structure)
          | Constr (ts1, constr1), Constr (ts2, constr2)
            when String.(constr1 = constr2) ->
            (match List.map2 ~f ts1 ts2 with
            | Ok ts ->
              `Ok
                (let%map ts = all ts in
                 Constr (ts, constr1))
            | Unequal_lengths -> `Unequal_structure)
          | Variant t1, Variant t2 ->
            `Ok
              (let%map t = f t1 t2 in
               Variant t)
          | _, _ -> `Unequal_structure
      end
    end

    include T
    include Type_former.Make (T)
  end

  module Types = struct
    module Label = String
    module Var = Type_var
    module Former = Type_former
  end

end
