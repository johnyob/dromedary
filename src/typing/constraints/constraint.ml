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
open Intf

(* ------------------------------------------------------------------------- *)

(* Include module types and type definitions from the [_intf] file. *)

include Constraint_intf

(* ------------------------------------------------------------------------- *)

module Make : Make_S = functor (Term_var : Term_var) (Types : Types) -> struct

(* ------------------------------------------------------------------------- *)

(* Add relevant modules from [Types]. *)

module Type_var = Types.Var
module Type_former = Types.Former
module Type = Types.Type

(* ------------------------------------------------------------------------- *)

(* The type [variable] in constraints. *)

type variable = int


(* See: https://github.com/janestreet/base/issues/121 *)
let post_incr r =
  let result = !r in
  Int.incr r;
  result
let fresh = 
  let next = ref 0 in
  fun () ->
    post_incr next

(* ------------------------------------------------------------------------- *)

(* The empty. Used for [Cst_false], which denotes a constraint that
   is never statisfied => has no defined value. *)
type empty = |

type _ t = 
  | Cst_true : unit t
  (** [true] *)
  | Cst_false : empty t
  (** [false] *)
  (* Cst_conj : 'ts constraint_list -> 'ts t *)
  (* constraint_list = Dependent_list (struct type nonrec 'a t = 'a t).t *)
  | Cst_conj : 'a t * 'b t -> ('a * 'b) t
  (** [C1 && C2] *)
  | Cst_eq : variable * variable -> unit t
  (** [a1 = a2] *)
  | Cst_exist : variable * 'a t -> 'a t
  (** [exists a. C] *)
  | Cst_forall : variable * 'a t -> 'a t
  (** [forall a. C] *)
  | Cst_instance : Term_var.t * variable -> Type.t list t
  (** [x <= a] *)
  | Cst_def : def_binding list * 'a t -> 'a t
  (** [def x1 : a1 and ... and xn : an in C] *)
  | Cst_let : 'a let_binding * 'b t  
      -> ((Term_var.t * Types.scheme) * 'a bound * 'b) t
  (** [let b1 ... bn [C]. (x1 : b1 and ... xn : bn) in C']. *)
  | Cst_map : 'a t * ('a -> 'b) -> 'b t
  (** [map C f]. *)
  | Cst_match : 'a t * 'b case list -> ('a * 'b list) t
  (** [match C with (... | (x1 : a1 ... xn : an) -> Ci | ...)]. *)

and binding = 
  { cb_tevar : Term_var.t
  ; cb_var : variable
  }

and def_binding = binding 

and 'a let_binding = 
  { clb_cst : 'a t
  ; clb_bs : binding list 
  }

and 'a bound = Type_var.t list * 'a t

and 'a case = 
  { ccase_bs : binding list
  ; ccase_cst : 'a t
  }


(* ------------------------------------------------------------------------- *)


(* 
TODO: Investigate the feasibility of using a dependent list:

module Dependent_list (T : sig type _ t end) = struct

  type _ t =
    | [] : unit t
    | (::) : 't T.t * 'ts t -> ('t * 'ts) t 

end 

Would require usage of the recursive module type-only trick:

module rec M : sig ... end = M 
and M_list : sig ... end = Dependent_list (M)

Some more dependent type tricks could be used to improve combinators. 
E.g. adding vectors to quantifiers for variables allows for well-typed
[Q a1 ... an. C].
*)

end 