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


open Size

type ('a, 'n) t = 
  | [] : ('a, Size.z) t
  | (::) : 'a * ('a, 'n) t -> ('a, 'n Size.s) t

let init : type a n. n Size.t -> f:(int -> a) -> (a, n) t =
  fun n ~f -> 
    let rec loop : type n. n Size.t -> int -> (a, n) t =
      fun n i -> match n with
      | Zero -> []
      | Suc n -> f i :: loop n (i + 1)
    in loop n 0 

let rec iter : type a n. (a, n) t -> f:(a -> unit) -> unit = 
  fun t ~f -> match t with
  | [] -> ()
  | x :: t -> f x; iter t ~f

let rec map : type a b n. (a, n) t -> f:(a -> b) -> (b, n) t = 
  fun t ~f -> match t with
  | [] -> []
  | x :: t -> f x :: map t ~f

let rec to_list : type a n. (a, n) t -> a list = 
  fun t -> match t with
  | [] -> []
  | x :: t -> x :: to_list t

let hd : type a n. (a, n Size.s) t -> a =
  fun t -> match t with
  | x :: _ -> x
