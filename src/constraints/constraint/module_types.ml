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
include Module_types_intf

module Type_former = struct
  include Type_former

  module Make (T : Basic) = struct
    include T

    module Ident = struct
      module T = struct
        type 'a t = 'a

        let return x = x
        let apply f x = f x
        let map = `Custom (fun t ~f -> f t)
      end

      include T
      include Applicative.Make (T)
    end

    module Endo_const (T : T) = struct
      module T = struct
        type 'a t = T.t -> T.t

        let return _ : 'a t = fun x -> x
        let apply t1 t2 : _ t = fun x -> t1 (t2 x)
        let map = `Define_using_apply
      end

      include T
      include Applicative.Make (T)
    end

    let map t ~f =
      let module Traverse = T.Traverse (Ident) in
      Traverse.traverse t ~f


    let iter t ~f = ignore (map t ~f : unit t)

    let fold (type a b) (t : a t) ~(f : a -> b -> b) ~(init : b) : b =
      let module Traverse =
        T.Traverse (Endo_const (struct
          type t = b
        end))
      in
      (Traverse.traverse t ~f) init


    let map2 t1 t2 ~f =
      let module Traverse = T.Traverse (Ident) in
      Traverse.traverse2 t1 t2 ~f


    exception Iter2

    let iter2_exn t1 t2 ~f =
      match map2 t1 t2 ~f with
      | `Ok _ -> ()
      | `Unequal_structure -> raise Iter2

    exception Fold2

    let fold2_exn (type a b c) (t1 : a t) (t2 : b t) ~(f : a -> b -> c -> c) ~(init : c) : c =
      let module Traverse =
        T.Traverse (Endo_const (struct
          type t = c
        end))
      in
      match (Traverse.traverse2 t1 t2 ~f) with
      | `Ok acc -> acc init
      | `Unequal_structure -> raise Fold2
  end
end
