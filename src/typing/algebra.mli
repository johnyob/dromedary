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

module Algebra : sig
  open Constraints.Module_types

  (** [Term_var] implements the abstract notion of variables in Dromedary's expressions
      (or "Terms"). *)
  module Term_var : Term_var with type t = string

  (** [Type_var] implements the abstract notion of type variables in Dromedary's types. *)
  module Type_var : Type_var with type t = string

  (** [Type_former] defines the various type formers for Dromedary's types.

      This notion of type former differs from that of our formal descriptions,
      since it describes:
      - Arrow types (or function types).
      - Tuple tuples.
      - Type constructors (or "Type formers" are referred to in the formalizations). *)
  module Type_former : sig
    type 'a t =
      | Arrow of 'a * 'a
      | Tuple of 'a list
      | Constr of 'a list * string
      | Variant of 'a
    [@@deriving sexp_of]

    include Type_former.S with type 'a t := 'a t
  end

  include
    Algebra
    with module Term_var := Term_var
     and type Types.Label.t = string
     and module Types.Var = Type_var
     and module Types.Former = Type_former
end
