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

module Type_former = struct
  module T = struct
    type 'a t =
      | Arrow of 'a * 'a
      | Int
    [@@deriving sexp_of]

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
        | Int -> return Int


      let traverse2 t1 t2 ~f =
        let open Let_syntax in
        match t1, t2 with
        | Arrow (t11, t12), Arrow (t21, t22) ->
          `Ok
            (let%map t1 = f t11 t21
             and t2 = f t12 t22 in
             Arrow (t1, t2))
        | Int, Int -> `Ok (return Int)
        | _, _ -> `Unequal_structure
    end
  end

  include T
  include Type_former.Make (T)
end

module Metadata = struct
  type t = unit [@@deriving sexp_of]

  let merge t1 _ = t1
end

module Unifier = struct
  include Unifier (Type_former) (Metadata)

  module Type = struct
    include Type

    let testable =
      Alcotest.testable
        (fun ppf t -> Sexp.pp ppf (sexp_of_t t))
        (fun t1 t2 -> compare t1 t2 = 0)
  end
end

module Type = struct
  type t =
    | Ttyp_var of int
    | Ttyp_int
    | Ttyp_arrow of t * t
  [@@deriving sexp_of, eq, qcheck]

  let arbitrary =
    QCheck.make gen ~print:(fun t -> sexp_of_t t |> Sexp.to_string_hum)


  let to_utype t =
    let table = Hashtbl.create (module Int) in
    let rec loop t =
      match t with
      | Ttyp_var x ->
        Hashtbl.find_or_add table x ~default:(Unifier.make_var Flexible)
      | Ttyp_int -> Unifier.make_former Int ()
      | Ttyp_arrow (t1, t2) ->
        let t1 = loop t1 in
        let t2 = loop t2 in
        Unifier.make_former (Arrow (t1, t2)) ()
    in
    loop t
end

let count = 10000

let ( =~ ) t1 t2 =
  let t1 = Type.to_utype t1 in
  let t2 = Type.to_utype t2 in
  try
    Ok
      (Unifier.unify t1 t2;
       t1)
  with
  | Unifier.Unify (t1, t2) -> Error (t1, t2)


let ( =~? ) t1 t2 = Result.is_ok (t1 =~ t2)

let occurs_check t =
  try
    Unifier.occurs_check t;
    false
  with
  | _ -> true


let decode_acyclic t =
  let open Type in
  Unifier.fold_acyclic
    t
    ~var:(fun var -> Ttyp_var (Unifier.Type.id var))
    ~former:(function
      | Arrow (t1, t2) -> Ttyp_arrow (t1, t2)
      | Int -> Ttyp_int)


let assume_unifiable t1 t2 =
  let t3 = t1 =~ t2 in
  QCheck.assume (Result.is_ok t3);
  let t3 = Result.ok t3 |> Option.value_exn in
  QCheck.assume (occurs_check t3);
  decode_acyclic t3


let test_unify_reflexivity =
  QCheck.Test.make
    ~count
    ~name:"Test unify : reflexivity"
    Type.arbitrary
    (fun t -> t =~? t)
  |> QCheck_alcotest.to_alcotest


let test_unify_symmetric =
  QCheck.Test.make
    ~count
    ~name:"Test unify : symmetric"
    QCheck.(pair Type.arbitrary Type.arbitrary)
    QCheck.(fun (t1, t2) -> t1 =~? t2 ==> (t2 =~? t1))
  |> QCheck_alcotest.to_alcotest


let test_unify_transitivity =
  QCheck.Test.make
    ~count
    ~name:"Test unify : transitivity"
    QCheck.(triple Type.arbitrary Type.arbitrary Type.arbitrary)
    (fun (t1, t2, t3) ->
      let t1_t2 = assume_unifiable t1 t2 in
      let t12_t3 = assume_unifiable t1_t2 t3 in
      t1 =~? t12_t3)
  |> QCheck_alcotest.to_alcotest


let test_unify_equality_impl_unify =
  QCheck.Test.make
    ~count
    ~name:"Test unify : equality => unifiable"
    QCheck.(pair Type.arbitrary Type.arbitrary)
    QCheck.(fun (t1, t2) -> Type.equal t1 t2 ==> (t1 =~? t2))
  |> QCheck_alcotest.to_alcotest


let tests =
  [ ( "Unifier"
    , [ test_unify_reflexivity
      ; test_unify_symmetric
      ; test_unify_transitivity
      ; test_unify_equality_impl_unify
      ] )
  ]
