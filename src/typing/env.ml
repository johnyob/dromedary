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
open Types

type t =
  { types : type_declaration map
  ; constrs : constructor_declaration map
  ; labels : label_declaration map
  }

and 'a map = (String.t, 'a, String.comparator_witness) Map.t

let empty =
  let empty_map () = Map.empty (module String) in
  { types = empty_map (); constrs = empty_map (); labels = empty_map () }


let find_constr env constr =
  Map.find env.constrs constr
  |> Result.of_option ~error:(`Unbound_constructor constr)


let find_label env label =
  Map.find env.labels label |> Result.of_option ~error:(`Unbound_label label)
