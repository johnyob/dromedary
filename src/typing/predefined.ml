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
open Constraint

module Type_former = struct
  open Algebra

  (* [t1 @-> t2] returns the arrow type [t1 -> t2]. *)
  let ( @-> ) x y = Type_former.Arrow (x, y)

  (* [tuple [t1; ...; tn]] returns the tuple type [t1 * ... * tn]. *)
  let tuple ts = Type_former.Tuple ts

  (* [constr [t1; ..; tn] constr'] returns the type former (or type constructor)
     [(t1, .., tn) constr']. *)
  let constr ts constr = Type_former.Constr (ts, constr)

  (* [int, bool] and [unit] are the type formers for the primitive [int, bool, unit]
     types. *)
  let int = Type_former.Constr ([], "int")
  let bool = Type_former.Constr ([], "bool")
  let unit = Type_former.Constr ([], "unit")
  let float = Type_former.Constr ([], "float")
  let char = Type_former.Constr ([], "char")
  let string = Type_former.Constr ([], "string")
  let exn = Type_former.Constr ([], "exn")
  let ref x = Type_former.Constr ([ x ], "ref")
  let variant x = Type_former.Variant x
  let present x = Type_former.Constr ([ x ], "present")
  let absent = Type_former.Constr ([], "absent")
end

open Type_former

let ( @-> ) t1 t2 = Type.former (t1 @-> t2)
let tuple ts = Type.former (tuple ts)
let constr ts constr_name = Type.former (constr ts constr_name)
let int = Type.former int
let bool = Type.former bool
let unit = Type.former unit
let float = Type.former float
let string = Type.former string
let char = Type.former char
let exn = Type.former exn
let ref t = Type.former (ref t)
let variant t = Type.former (variant t)
let row_cons label t1 t2 = Type.Row_cons (label, t1, t2)
let row_uniform t = Type.Row_uniform t
let present t = Type.former (present t)
let absent = Type.former absent
