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

type ('a, 'n) t = 
  | [] : ('a, Size.z) t
  | (::) : 'a * ('a, 'n) t -> ('a, 'n Size.s) t

val init : 'n Size.t -> f:(int -> 'a) -> ('a, 'n) t

val map : ('a, 'n) t -> f:('a -> 'b) -> ('b, 'n) t

val iter : ('a, _) t -> f:('a -> unit) -> unit

val to_list : ('a, _) t -> 'a list

val hd : ('a, 'n Size.s) t -> 'a