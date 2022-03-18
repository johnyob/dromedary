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

open! Base

(* [Module_types] provides the interfaces required "abstract" constraints. *)

module Module_types = Module_types
open Module_types

module Make (Algebra : Algebra) = struct
  open Algebra

  (* Add relevant modules from [Types]. *)

  module Label = struct
    include Types.Label

    let sexp_of_t = comparator.sexp_of_t
  end

  module Type_var = Types.Var
  module Type_former = Types.Former

  type variable = int [@@deriving sexp_of]

  let fresh =
    let post_incr r =
      let result = !r in
      Int.incr r;
      result
    in
    let next = ref 0 in
    fun () -> post_incr next


  (* The module [Type] provides the concrete representation of types
     (using constraint type variables) in constraints. 

     It is the free monad of the functor [Type_former.t].

     History: This representation was initially used in constraints [t],
     however, the refactor for "Sharing" now uses [Shallow_type.t].
     We however, still use [Type] for a rich interface. 
  *)

  module Type = struct
    (* [t] represents the type defined by the grammar: 
       t ::= ɑ | (t, .., t) F *)
    type t =
      | Var of variable
      | Former of t Type_former.t
      | Row_cons of Label.t * t * t
      | Row_uniform of t
      | Mu of variable * t
    [@@deriving sexp_of]

    (* [var a] returns the representation of the type variable [a]. *)
    let var var = Var var

    (* [former f] returns the representation of the applied type former [f]. *)
    let former former = Former former
    let mu var t = Mu (var, t)
  end

  (* The module [Shallow_type] provides the shallow type definition
     used within constraints. 
     
     This encoding is required for "(Explicit) sharing" of types
     within constraints.

     Types from [Type] are often referred to as "deep" types. 
  *)

  module Shallow_type = struct
    type t =
      | Former of variable Type_former.t
      | Row_cons of Label.t * variable * variable
      | Row_uniform of variable
      | Mu of variable
    [@@deriving sexp_of]

    type binding = variable * t [@@deriving sexp_of]

    module Ctx = struct
      type t = variable list * binding list [@@deriving sexp_of]


      let merge (vars1, bindings1) (vars2, bindings2) =
        vars1 @ vars2, bindings1 @ bindings2
    end

    type encoded_type = Ctx.t * variable [@@deriving sexp_of]

    (* [of_type type_] returns the shallow encoding [Θ |> ɑ] of the 
       deep type [type_]. *)
    let of_type type_ : encoded_type =
      let variables = ref [] in
      let fresh () =
        let var = fresh () in
        variables := var :: !variables;
        var
      in
      let bindings = ref [] in
      let bind var shallow_type =
        bindings := (var, shallow_type) :: !bindings
      in
      let rec loop t =
        match t with
        | Type.Var var -> var
        | Type.Former former ->
          let var = fresh () in
          bind var (Former (Type_former.map former ~f:loop));
          var
        | Type.Row_cons (label, t1, t2) ->
          let var = fresh () in
          bind var (Row_cons (label, loop t1, loop t2));
          var
        | Type.Row_uniform t ->
          let var = fresh () in
          bind var (Row_uniform (loop t));
          var
        | Type.Mu (var, t) ->
          bind var (Mu (loop t));
          var
      in
      let var = loop type_ in
      (!variables, !bindings), var
  end

  type existential_context = Shallow_type.Ctx.t [@@deriving sexp_of]
  type universal_context = variable list [@@deriving sexp_of]
  type equations = (Type.t * Type.t) list [@@deriving sexp_of]
  type 'a bound = Type_var.t list * 'a

  type term_binding = Term_var.t * Types.scheme
  and 'a term_let_binding = term_binding list * 'a bound
  and 'a term_let_rec_binding = term_binding * 'a bound

  (* ['a t] is a constraint with value type ['a]. *)
  type _ t =
    | True : unit t
    | Return : 'a -> 'a t
    | Conj : 'a t * 'b t -> ('a * 'b) t
    | Eq : variable * variable -> unit t
    | Exist : existential_context * 'a t -> 'a t
    | Forall : universal_context * 'a t -> 'a t
    | Instance : Term_var.t * variable -> Types.Type.t list t
    | Def : binding list * 'a t -> 'a t
    | Let : 'a let_binding list * 'b t -> ('a term_let_binding list * 'b) t
    | Let_rec :
        'a let_rec_binding list * 'b t
        -> ('a term_let_rec_binding list * 'b) t
    | Map : 'a t * ('a -> 'b) -> 'b t
    | Decode : variable -> Types.Type.t t
    | Implication : equations * 'a t -> 'a t

  and binding = Term_var.t * variable
  and def_binding = binding

  and 'a let_binding =
    | Let_binding of
        { universal_context : universal_context
        ; existential_context : existential_context
        ; is_non_expansive : bool
        ; bindings : binding list
        ; in_ : 'a t
        ; equations : equations
        }

  and 'a let_rec_binding =
    | Let_rec_mono_binding of
        { universal_context : universal_context
        ; existential_context : existential_context
        ; binding : binding
        ; in_ : 'a t
        }
    | Let_rec_poly_binding of
        { universal_context : universal_context
        ; annotation : Shallow_type.Ctx.t * variable
        ; term_var : Term_var.t
        ; in_ : 'a t
        }


  let rec sexp_of_t : type a. a t -> Sexp.t =
   fun t ->
    match t with
    | Return _ -> [%sexp Return]
    | True -> [%sexp True]
    | Conj (t1, t2) -> [%sexp Conj (t1 : t), (t2 : t)]
    | Eq (var1, var2) -> [%sexp Eq (var1 : variable), (var2 : variable)]
    | Exist (ctx, t) -> [%sexp Exist (ctx : existential_context), (t : t)]
    | Forall (vars, t) -> [%sexp Forall (vars : variable list), (t : t)]
    | Instance (x, a) -> [%sexp Instance (x : Term_var.t), (a : variable)]
    | Def (bindings, t) -> [%sexp Def (bindings : binding list), (t : t)]
    | Let (let_bindings, t) ->
      [%sexp Let (let_bindings : let_binding list), (t : t)]
    | Let_rec (let_rec_bindings, t) ->
      [%sexp Let_rec (let_rec_bindings : let_rec_binding list), (t : t)]
    | Map (t, _f) -> [%sexp Map (t : t)]
    | Decode a -> [%sexp Decode (a : variable)]
    | Implication (equations, t) ->
      [%sexp Implication (equations : (Type.t * Type.t) list), (t : t)]


  and sexp_of_binding = [%sexp_of: Term_var.t * variable]

  and sexp_of_def_binding def_binding = sexp_of_binding def_binding

  and sexp_of_let_binding : type a. a let_binding -> Sexp.t =
   fun (Let_binding
         { universal_context
         ; existential_context
         ; is_non_expansive
         ; bindings
         ; in_
         ; equations
         }) ->
    [%sexp
      Let_binding (universal_context : universal_context)
      , (existential_context : existential_context)
      , (bindings : binding list)
      , (is_non_expansive : bool)
      , (in_ : t)
      , (equations : (Type.t * Type.t) list)]


  and sexp_of_let_rec_binding : type a. a let_rec_binding -> Sexp.t =
   fun binding ->
    match binding with
    | Let_rec_mono_binding
        { universal_context; existential_context; binding; in_ } ->
      [%sexp
        Let_rec_binding (universal_context : universal_context)
        , (existential_context : existential_context)
        , (binding : binding)
        , (in_ : t)]
    | Let_rec_poly_binding { universal_context; annotation; term_var; in_ } ->
      [%sexp
        Let_rec_poly_binding (universal_context : universal_context)
        , (annotation : Shallow_type.encoded_type)
        , (term_var : Term_var.t)
        , (in_ : t)]


  (* ['a t] forms an applicative functor, allowing us to combine
     many constraints into a single one using [let%map]:

     {[
       val pat : Typedtree.pattern Constraint.t
       val exp : Typedtree.expression Constraint.t

       let%map pat and exp in
       Texp_fun (pat, ..., exp)
     ]}  
  *)

  include Applicative.Make (struct
    type nonrec 'a t = 'a t

    let return x = Return x
    let map = `Custom (fun t ~f -> Map (t, f))
    let apply t1 t2 = Map (Conj (t1, t2), fun (f, x) -> f x)
  end)

  (* [both] is explicitly defined for efficiency reasons. *)
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

  (* [&~] is an infix alias for [both] *)
  let ( &~ ) = both

  (* [t1 >> t2 >> ... >> tn] solves [t1, ..., tn] yielding the value 
     of [tn]. It is the monodial operator of constraints. *)
  let ( >> ) t1 t2 = t1 &~ t2 >>| snd

  (* [a =~ a'] is an infix alias for [Eq], denoting the equality
     constraint on type variables. *)
  let ( =~ ) a1 a2 = Eq (a1, a2)

  let ( =~= ) a1 shallow_type =
    let a2 = fresh () in
    Exist (([ a2 ], [ a2, shallow_type ]), a1 =~ a2)


  let ( =~- ) a1 type_ =
    let bindings, a2 = Shallow_type.of_type type_ in
    Exist (bindings, a1 =~ a2)


  (* [inst x a] is the constraint that instantiates [x] to [a].
     It returns the type variable substitution. *)
  let inst x a = Instance (x, a)

  (* [decode a] is a constraint that evaluates to the decoded
     type of [a]. *)
  let decode a = Decode a

  (* [exists ~ctx t] binds existential context [ctx] in [t]. *)
  let exists ~ctx t =
    match ctx with
    | [], [] -> t
    | ctx ->
      (match t with
      | Exist (ctx', t) -> Exist (Shallow_type.Ctx.merge ctx ctx', t)
      | t -> Exist (ctx, t))


  (* [forall ~ctx t] binds universal context [ctx] in [t]. *)
  let forall ~ctx t =
    match ctx with
    | [] -> t
    | vars ->
      (match t with
      | Forall (vars', t) -> Forall (vars @ vars', t)
      | t -> Forall (vars, t))


  (* [x #= a] yields the binding that binds [x] to [a]. *)
  let ( #= ) x a : binding = x, a

  (* [def ~bindings ~in_] binds [bindings] in the constraint [in_]. *)
  let def ~bindings ~in_ = Def (bindings, in_)

  let ( #=> ) equations t =
    match equations with
    | [] -> t
    | equations -> Implication (equations, t)


  (* [let_ ~bindings ~in_] binds the let bindings [bindings] in the constraint [in_]. *)
  let let_ ~bindings ~in_ = Let (bindings, in_)

  (* [let_rec ~bindings ~in_] recursively binds the let bindings [bindings] in the 
     constraint [in_]. *)
  let let_rec ~bindings ~in_ = Let_rec (bindings, in_)

  module Binding = struct
    type ctx = universal_context * existential_context [@@deriving sexp_of]

    let let_
        ~ctx:(universal_context, existential_context)
        ~is_non_expansive
        ~bindings
        ~in_
        ~equations
      =
      Let_binding
        { universal_context
        ; existential_context
        ; is_non_expansive
        ; bindings
        ; in_
        ; equations
        }


    let let_mrec ~ctx:(universal_context, existential_context) ~binding ~in_ =
      Let_rec_mono_binding
        { universal_context; existential_context; binding; in_ }


    let let_prec ~universal_ctx ~annotation ~term_var ~in_ =
      Let_rec_poly_binding
        { universal_context = universal_ctx; annotation; term_var; in_ }
  end
end
