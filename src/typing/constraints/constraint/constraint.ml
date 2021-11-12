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

open Misc
open Base

(* ------------------------------------------------------------------------- *)

(* [Intf] provides the interfaces required for constraints. *)

module Intf = Intf

(* ------------------------------------------------------------------------- *)

open Intf

module Make (Term_var : Term_var) (Types : Types) = struct
  (* --------------------------------------------------------------------- *)

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

  (* --------------------------------------------------------------------- *)

  (* ['a t] is a constraint with value type ['a]. *)

  type _ t =
    | Cst_true : unit t 
    | Cst_conj : 'a t * 'b t -> ('a * 'b) t 
    | Cst_eq : Type.t * Type.t -> unit t 
    | Cst_exist : variable list * 'a t -> 'a t 
    | Cst_forall : variable list * 'a t -> 'a t 
    | Cst_instance : Term_var.t * Type.t -> Types.Type.t list t 
    | Cst_def : def_binding list * 'a t -> 'a t
    | Cst_let : 'a let_binding * 'b t -> (term_binding list * 'a bound * 'b) t
    | Cst_map : 'a t * ('a -> 'b) -> 'b t 
    | Cst_match : 'a t * 'b case list -> ('a * 'b list) t
    | Cst_decode : Type.t -> Types.Type.t t

  and term_binding = Term_var.t * Types.scheme

  and binding = Term_var.t * Type.t

  and def_binding = binding

  and 'a scheme =
    { csch_rigid_vars : variable list
    ; csch_flexible_vars : variable list
    ; csch_cst : 'a t
    }

  and 'a let_binding =
    { clb_sch : 'a scheme
    ; clb_bs : binding list
    }

  and 'a bound = Type_var.t list * 'a

  and 'a case =
    { ccase_bs : binding list
    ; ccase_cst : 'a t
    }
  (* ----------------------------------------------------------------------*)

  (* Constraints ['a t] form an applicative functor. *)

  include Applicative.Make (struct
    type nonrec 'a t = 'a t

    let return x = Cst_map (Cst_true, fun () -> x)
    let map = `Custom (fun t ~f -> Cst_map (t, f))
    let apply t1 t2 = Cst_map (Cst_conj (t1, t2), fun (f, x) -> f x)
  end)

  let both t1 t2 = Cst_conj (t1, t2)

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

  (* The function [&~] is an infix alias for [both] *)

  let ( &~ ) = both

  (* The function [>>] constructs a constraint from [t1] and [t2], returning
     the value of [t2]. *)

  let ( >> ) t1 t2 = t1 &~ t2 >>| snd
  let ( =~ ) typ1 typ2 = Cst_eq (typ1, typ2)
  let inst var typ = Cst_instance (var, typ)
  let decode typ = Cst_decode typ

  (* --------------------------------------------------------------------- *)

  (* Quantifiers, binders and continuations *)

  module Continuation = struct
    (* A continuation of the type [('a, 'b) cont] is a continuation for
       constraint computations.

       An example usage is binders: e.g. [exists]. However, we also use them
       for typing patterns, etc.

       As with standard continuations, they form a monadic structure. *)
    type nonrec ('a, 'b) t = ('a -> 'b t) -> 'b t

    include Monad.Make2 (struct
      type nonrec ('a, 'b) t = ('a, 'b) t

      let return x k = k x
      let bind t ~f k = t (fun a -> f a k)
      let map = `Define_using_bind
    end)
  end

  (* [('n, 'a) binder] is a binder that binds ['n] variables. *)

  type ('n, 'a) binder = ('n variables, 'a) Continuation.t

  (* ['n variables] encodes the type of a list containing n variables
     (where n is the type-level natural number representation). *)
  and 'n variables = (variable, 'n) Sized_list.t

  (* [('m, 'n, 'a) binder2] is the 2 kinded version of [binder], bindings ['m]
       and ['n] rigid and flexible variables, respectively. *)
  type ('m, 'n, 'a) binder2 = ('m variables * 'n variables, 'a) Continuation.t

  let exists n binder =
    let n_vars = Sized_list.init n ~f:(fun _ -> fresh ()) in
    let t = binder n_vars
    and vars = Sized_list.to_list n_vars in
    match t with
    | Cst_exist (vars', t) -> Cst_exist (vars @ vars', t)
    | _ -> Cst_exist (vars, t)


  let forall n binder =
    let n_vars = Sized_list.init n ~f:(fun _ -> fresh ()) in
    let t = binder n_vars
    and vars = Sized_list.to_list n_vars in
    match t with
    | Cst_forall (vars', t) -> Cst_forall (vars @ vars', t)
    | _ -> Cst_forall (vars, t)


  (* --------------------------------------------------------------------- *)

  (* Environmental constraints (binders) *)

  let ( #= ) x typ : binding = x, typ
  let def bindings cst = Cst_def (bindings, cst)

  let scheme ~rigid ~flexible csch_cst =
    { csch_rigid_vars = rigid; csch_flexible_vars = flexible; csch_cst }


  let let_ m n cst1 bindings cst2 =
    (* Initialize [m] rigid variables and [n] flexible variables. *)
    let m_rigid_vars = Sized_list.init m ~f:(fun _ -> fresh ())
    and n_flexible_vars = Sized_list.init n ~f:(fun _ -> fresh ()) in
    (* Pass variables to the bindings binder and first constraint *)
    let cst1 = cst1 (m_rigid_vars, n_flexible_vars)
    and bindings = bindings (m_rigid_vars, n_flexible_vars) in
    (* Build let constraint. *)
    let sch =
      scheme
        ~rigid:(Sized_list.to_list m_rigid_vars)
        ~flexible:(Sized_list.to_list n_flexible_vars)
        cst1
    in
    Cst_let ({ clb_sch = sch; clb_bs = bindings }, cst2)
end

(* TODO: Investigate the feasibility of using a dependent list:

   module Dependent_list (T : sig type _ t end) = struct

   type _ t = | [] : unit t | (::) : 't T.t * 'ts t -> ('t * 'ts) t

   end

   Would require usage of the recursive module type-only trick:

   module rec M : sig ... end = M and M_list : sig ... end = Dependent_list
   (M) *)
