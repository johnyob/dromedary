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

(* ------------------------------------------------------------------------- *)

(* [Intf] provides the interfaces required for constraints. *)

module Module_types = Module_types

(* ------------------------------------------------------------------------- *)

open Module_types

module Make (Algebra : Algebra) = struct
  (* --------------------------------------------------------------------- *)

  open Algebra

  (* Add relevant modules from [Types]. *)

  module Type_var = Types.Var
  module Type_former = Types.Former

  (* --------------------------------------------------------------------- *)

  (* The type [variable] in constraints. *)

  type variable = int

  (* See: https://github.com/janestreet/base/issues/121 *)
  let post_incr r =
    let result = !r in
    Int.incr r;
    result


  let fresh =
    let next = ref 0 in
    fun () -> post_incr next


  (* --------------------------------------------------------------------- *)

  (* A concrete representation of types using constraint variables. It is the
     free monad of the functor [Type_former.t] with variables [variable].

     While previously, we have stated that such a construct is unweidly, using
     this provides a richer interface between constraints and the rest of the
     type checker.

     Moreover, this provides a nicer translation between constraints and
     "graphic types".

     Graphic type nodes consist of a "structure", either a variable of a type
     former (isomorphic to what we define below, given a mapping between
     constraint variables and graphic nodes.) *)

  module Type = struct
    type t =
      | Var of variable
      | Form of t Type_former.t

    let var x = Var x
    let form f = Form f
  end

  module Shallow_type = struct
    type t = variable Type_former.t
    type binding = variable * t option
    type context = binding list

    let of_type t =
      let bindings = ref [] in
      let rec loop t =
        match t with
        | Type.Var v -> v
        | Type.Form form ->
          let var = fresh () in
          let form = Type_former.map form ~f:loop in
          bindings := (var, Some form) :: !bindings;
          var
      in
      let var = loop t in
      !bindings, var
  end

  (* --------------------------------------------------------------------- *)

  (* ['a t] is a constraint with value type ['a]. *)

  type _ t =
    | True : unit t (** [true] *)
    | Conj : 'a t * 'b t -> ('a * 'b) t (** [C₁ && C₂] *)
    | Eq : variable * variable -> unit t (** [ɑ₁ = ɑ₂] *)
    | Exist : Shallow_type.binding list * 'a t -> 'a t (** [exists Δ. C] *)
    | Forall : variable list * 'a t -> 'a t (** [forall Θ. C] *)
    | Instance : Term_var.t * variable -> Types.Type.t list t (** [x <= ɑ] *)
    | Def : binding list * 'a t -> 'a t
        (** [def x1 : t1 and ... and xn : tn in C] *)
    | Let : 'a let_binding * 'b t -> ('a term_let_binding * 'b) t
        (** [let ∀ Θ ∃ Δ. C => (x₁ : Ɣ₁ and ... xₘ : Ɣₘ) in C']. *)
    | Letn : 'a let_binding list * 'b t -> ('a term_let_binding list * 'b) t
        (** [let Γ in C] *)
    | Let_rec : 'a let_rec_binding list * 'b t -> ('a term_let_rec_binding list * 'b) t
        (** [let rec Γ in C] *)
    | Map : 'a t * ('a -> 'b) -> 'b t (** [map C f]. *)
    | Match : 'a t * 'b case list -> ('a * 'b list) t
        (** [match C with (... | (x₁ : ɑ₁ ... xₙ : ɑₙ) -> Cᵢ | ...)]. *)
    | Decode : variable -> Types.Type.t t (** [decode ɑ] *)

  and binding = Term_var.t * variable

  and def_binding = binding

  and 'a let_binding =
    | Let_binding of
        { rigid_vars : variable list
        ; flexible_vars : Shallow_type.binding list
        ; bindings : binding list
        ; in_ : 'a t
        }

  and 'a let_rec_binding = 
    | Let_rec_binding of
      { rigid_vars : variable list
      ; flexible_vars : Shallow_type.binding list
      ; binding : binding
      ; in_ : 'a t
      }

  and 'a case =
    | Case of
        { bindings : binding list
        ; in_ : 'a t
        }

  and 'a bound = Type_var.t list * 'a

  and term_binding = Term_var.t * Types.scheme

  and 'a term_let_binding = term_binding list * 'a bound

  and 'a term_let_rec_binding = term_binding * 'a bound

  (* ----------------------------------------------------------------------*)

  (* Constraints ['a t] form an applicative functor. *)

  include Applicative.Make (struct
    type nonrec 'a t = 'a t

    let return x = Map (True, fun () -> x)
    let map = `Custom (fun t ~f -> Map (t, f))
    let apply t1 t2 = Map (Conj (t1, t2), fun (f, x) -> f x)
  end)

  let both t1 t2 = Conj (t1, t2)

  module Open_on_rhs_intf = struct
    module type S = sig end
  end

  module Let_syntax = struct
    let return = return

    include Applicative_infix

    module Let_syntax = struct
      let return = return
      let map = map
      let both = both

      module Open_on_rhs = struct end
    end
  end

  (* --------------------------------------------------------------------- *)

  (* Combinators *)

  module Continuation = struct
    type nonrec ('a, 'b) t = ('a -> 'b t) -> 'b t

    include Monad.Make2 (struct
      type nonrec ('a, 'b) t = ('a, 'b) t

      let return x k = k x
      let bind t ~f k = t (fun a -> f a k)
      let map = `Define_using_bind
    end)

    let lift t = t
    let run t = t
  end

  type 'n variables = (variable, 'n) Sized_list.t
  type 'a binder = (variable, 'a) Continuation.t
  type ('n, 'a) bindern = ('n variables, 'a) Continuation.t

  (* The function [&~] is an infix alias for [both] *)
  let ( &~ ) = both

  (* The function [>>] constructs a constraint from [t1] and [t2], returning
     the value of [t2]. *)
  let ( >> ) t1 t2 = t1 &~ t2 >>| snd
  let ( =~ ) var1 var2 = Eq (var1, var2)
  let inst var1 var2 = Instance (var1, var2)
  let decode var = Decode var

  let exists bindings t =
    match t with
    | Exist (bindings', t) -> Exist (bindings @ bindings', t)
    | t -> Exist (bindings, t)


  let of_type type_ =
    Continuation.lift (fun binder ->
        let bindings, var = Shallow_type.of_type type_ in
        exists bindings (binder var))


  let existsn n binder =
    let variables = Sized_list.init n ~f:(fun _ -> fresh ()) in
    exists
      (Sized_list.to_list variables |> List.map ~f:(fun v -> v, None))
      (binder variables)


  let exists1 binder =
    let v = fresh () in
    exists [ v, None ] (binder v)


  let forall vars t =
    match t with
    | Forall (vars', t) -> Forall (vars @ vars', t)
    | t -> Forall (vars, t)


  let foralln n binder =
    let variables = Sized_list.init n ~f:(fun _ -> fresh ()) in
    forall (Sized_list.to_list variables) (binder variables)


  let forall1 binder =
    let v = fresh () in
    forall [ v ] (binder v)


  let ( #= ) x typ : binding = x, typ
  let def ~bindings ~in_ = Def (bindings, in_)

  let let_ ~rigid ~flexible ~bindings:(in1_, bindings) ~in2_ =
    Let
      ( Let_binding
          { rigid_vars = rigid; flexible_vars = flexible; bindings; in_ = in1_ }
      , in2_ )
end
