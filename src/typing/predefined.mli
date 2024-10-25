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

module Type_former : sig
  open Algebra

  (** [t1 @-> t2] returns the type former for the arrow type [t1 -> t2]. *)
  val ( @-> ) : 'a -> 'a -> 'a Type_former.t

  (** [tuple [t1; ...; tn]] returns the type former for the
      tuple [t1 * .. * tn]. *)
  val tuple : 'a list -> 'a Type_former.t

  (** [constr [t1; ...; tn] constr_name] returns the type former the
      constructor [(t1, .., tn) constr_name]. *)
  val constr : 'a list -> string -> 'a Type_former.t

  (** Primitive / Constant type formers: [int, bool, unit, float],
      and [char, string]. *)
  val int : 'a Type_former.t

  val bool : 'a Type_former.t
  val unit : 'a Type_former.t
  val float : 'a Type_former.t
  val char : 'a Type_former.t
  val string : 'a Type_former.t

  (** Pre-defined type formers for side-effecting primitives. *)
  val exn : 'a Type_former.t

  val ref : 'a -> 'a Type_former.t

  (** [variant row] returns the type former for the
      polymorphic variant [[(>|=|<) row]]. *)
  val variant : 'a -> 'a Type_former.t

  (** Pre-defined type formers used to encode presence
      information. *)
  val present : 'a -> 'a Type_former.t

  val absent : 'a Type_former.t
end

(** [t1 @-> t2] returns the the type [t1 -> t2]. *)
val ( @-> ) : Type.t -> Type.t -> Type.t

(** [tuple [t1; ...; tn]] returns the type [t1 * .. * tn]. *)
val tuple : Type.t list -> Type.t

(** [constr [t1; ...; tn] constr_name] returns the type [(t1, .., tn) constr_name]. *)
val constr : Type.t list -> string -> Type.t

(** Primitive / Constant type [int, bool, unit, float], and [string]. *)
val int : Type.t

val bool : Type.t
val unit : Type.t
val float : Type.t
val char : Type.t
val string : Type.t

(** Pre-defined types for exceptions [exn]. *)
val exn : Type.t

(** [ref t] returns the type [t ref]. *)
val ref : Type.t -> Type.t

(** [variant row] returns the type [[(>|=|<) row]]. *)
val variant : Type.t -> Type.t

(** [row_cons label t1 t2] returns the row [label:t1 :: t2]. *)
val row_cons : string -> Type.t -> Type.t -> Type.t

(** [row_uniform t] returns the row [∂t]. *)
val row_uniform : Type.t -> Type.t

(** [present] and [absent] are used to encode presence information
    in rows. *)
val present : Type.t -> Type.t

val absent : Type.t
