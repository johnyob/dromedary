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
include Computation_intf

module Input = struct
  type t =
    { env : Env.t
    ; substitution : Substitution.t
    }

  let make ~env ~substitution = { env; substitution }
  let env t = t.env
  let substitution t = t.substitution

  let extend_substitution t ~substitution =
    { t with substitution = Substitution.merge t.substitution substitution }
end

module Expression = struct
  module T = struct
    type 'a t = Input.t -> ('a, Sexp.t) Result.t

    let return x _input = Ok x

    let bind t ~f input =
      let%bind.Result x = t input in
      f x input


    let map = `Define_using_bind
  end

  module Computation = struct
    include T
    include Monad.Make (T)
  end

  include Computation

  let of_result result ~message : 'a t =
   fun _input -> Result.map_error result ~f:message


  let const x = return (Constraint.return x)
  let fail err : 'a t = fun _input -> Error err
  let env : Env.t t = fun input -> Ok (Input.env input)

  let find_label label : Types.label_declaration t =
   fun input ->
    Env.find_label (Input.env input) label
    |> Result.map_error ~f:(fun (`Unbound_label _label) -> assert false)


  let find_constr name : Types.constructor_declaration t =
   fun input ->
    Env.find_constr (Input.env input) name
    |> Result.map_error ~f:(fun (`Unbound_constructor _constr) -> assert false)


  let substitution : Substitution.t t =
   fun input -> Ok (Input.substitution input)


  let extend_substitution t ~substitution input =
    t (Input.extend_substitution input ~substitution)


  let find_var var : Constraint.variable t =
   fun input ->
    Substitution.find_var (Input.substitution input) var
    |> Result.map_error ~f:(fun (`Unbound_type_variable _var) -> assert false)


  module Binder = struct
    module T = struct
      type 'a t =
        { f :
            'b.
            ('a -> 'b Constraint.t Computation.t)
            -> 'b Constraint.t Computation.t
        }

      let return x = { f = (fun k -> k x) }
      let bind t ~f = { f = (fun k -> t.f (fun x -> (f x).f k)) }
      let map = `Define_using_bind
    end

    include T
    include Monad.Make (T)

    let exists () =
      { f =
          (fun k ->
            let var = Constraint.fresh () in
            let%map.Computation t = k var in
            Constraint.exists ~ctx:([ var ], []) t)
      }


    let forall () =
      { f =
          (fun k ->
            let var = Constraint.fresh () in
            let%map.Computation t = k var in
            Constraint.forall ~ctx:[ var ] t)
      }


    let exists_ctx ~ctx =
      { f =
          (fun k ->
            let%map.Computation t = k () in
            Constraint.exists ~ctx t)
      }


    let exists_vars vars = exists_ctx ~ctx:(vars, [])

    let forall_ctx ~ctx =
      { f =
          (fun k ->
            let%map.Computation t = k () in
            Constraint.forall ~ctx t)
      }


    let of_type type_ =
      { f =
          (fun k ->
            let ctx, var = Constraint.Shallow_type.of_type type_ in
            let%map.Computation t = k var in
            Constraint.exists ~ctx t)
      }


    let run t ~cc = t.f cc

    module Let_syntax = struct
      let return = return
      let ( >>| ) = Constraint.( >>| )
      let ( <*> ) = Constraint.( <*> )

      let ( let& ) computation f =
        { f =
            (fun k ->
              let%bind.Computation x = computation in
              (f x).f k)
        }


      module Let_syntax = struct
        let return = return
        let map = Constraint.map
        let both = Constraint.both
        let bind = bind
      end
    end
  end

  let run t ~env = t (Input.make ~env ~substitution:Substitution.empty)

  module Let_syntax = struct
    let return = return
    let ( >>| ) = Constraint.( >>| )
    let ( <*> ) = Constraint.( <*> )
    let ( let@ ) binder f = Binder.run binder ~cc:f

    module Let_syntax = struct
      let return = return
      let map = Constraint.map
      let both = Constraint.both
      let bind = bind
    end
  end
end

module Fragment = struct
  open Constraint

  type t =
    { universal_context : universal_context
    ; existential_context : existential_context
    ; term_bindings : Constraint.variable String.Map.t
    ; equations : equations
    ; substitution : Constraint.variable String.Map.t
    }

  let empty =
    { universal_context = []
    ; existential_context = [], []
    ; term_bindings = String.Map.empty
    ; equations = []
    ; substitution = String.Map.empty
    }


  let merge t1 t2 =
    let exception Duplicate_term_var of string in
    let exception Duplicate_type_var of string in
    try
      let term_bindings =
        Map.merge_skewed
          t1.term_bindings
          t2.term_bindings
          ~combine:(fun ~key _ _ -> raise (Duplicate_term_var key))
      in
      let universal_context =
        t1.universal_context @ t2.universal_context
      in
      let existential_context =
        Shallow_type.Ctx.merge t1.existential_context t2.existential_context
      in
      let equations = t1.equations @ t2.equations in
      let substitution =
        Map.merge_skewed
          t1.substitution
          t2.substitution
          ~combine:(fun ~key _ _ -> raise (Duplicate_type_var key))
      in
      Ok
        { universal_context
        ; existential_context
        ; term_bindings
        ; equations
        ; substitution
        }
    with
    | Duplicate_term_var term_var -> Error (`Duplicate_term_var term_var)
    | Duplicate_type_var var -> Error (`Duplicate_type_var var)


  let of_existential_ctx existential_context =
    { empty with existential_context }


  let of_term_binding x a =
    { empty with term_bindings = Map.singleton (module String) x a }


  let to_bindings t =
    ( t.universal_context
    , t.existential_context
    , t.equations
    , t.term_bindings |> Map.to_alist |> List.map ~f:(fun (x, a) -> x #= a)
    , Substitution.of_map t.substitution )
end

module Pattern = struct
  module T = struct
    type 'a t = (Fragment.t * 'a) Expression.t

    let return x = Expression.return (Fragment.empty, x)

    let bind t ~f =
      let%bind.Expression fragment1, x = t in
      let%bind.Expression fragment2, y = f x in
      Expression.of_result
        ~message:(fun _ -> assert false)
        (let%map.Result fragment = Fragment.merge fragment1 fragment2 in
         fragment, y)


    let map = `Define_using_bind
  end

  module Computation = struct
    include T
    include Monad.Make (T)
  end

  include Computation

  let lift m : 'a t =
   fun input -> Result.(m input >>| fun x -> Fragment.empty, x)


  let run t input = t input
  let of_result result ~message = lift (Expression.of_result result ~message)
  let const x = lift (Expression.const x)
  let fail err = lift (Expression.fail err)
  let env = lift Expression.env
  let find_label label = lift (Expression.find_label label)
  let find_constr name = lift (Expression.find_constr name)
  let substitution = lift Expression.substitution
  let find_var var = lift (Expression.find_var var)

  let extend_substitution t ~substitution input =
    t (Input.extend_substitution input ~substitution)


  let write fragment : unit t = fun _input -> Ok (fragment, ())
  let extend x a = write (Fragment.of_term_binding x a)
  let assert_ equations = write Fragment.{ empty with equations }

  let extend_fragment_substitution substitution =
    write
      Fragment.{ empty with substitution = Substitution.to_map substitution }


  module Binder = struct
    include Computation

    let exists () =
      let var = Constraint.fresh () in
      let%bind.Computation () =
        write (Fragment.of_existential_ctx ([ var ], []))
      in
      return var


    let forall () =
      let var = Constraint.fresh () in
      let%bind.Computation () =
        write Fragment.{ empty with universal_context = [ var ] }
      in
      return var


    let exists_ctx ~ctx =
      write (Fragment.of_existential_ctx ctx)


    let exists_vars vars = exists_ctx ~ctx:(vars, [])

    let forall_ctx ~ctx =
      write Fragment.{ empty with universal_context = ctx }


    let of_type type_ =
      let ctx, var = Constraint.Shallow_type.of_type type_ in
      let%bind.Computation () =
        write (Fragment.of_existential_ctx ctx)
      in
      return var


    module Let_syntax = struct
      let return = return
      let ( >>| ) = Constraint.( >>| )
      let ( <*> ) = Constraint.( <*> )
      let ( let& ) computation f = bind computation ~f

      module Let_syntax = struct
        let return = return
        let map = Constraint.map
        let both = Constraint.both
        let bind = bind
      end
    end
  end

  module Let_syntax = struct
    let return = return
    let ( >>| ) = Constraint.( >>| )
    let ( <*> ) = Constraint.( <*> )
    let ( let@ ) binder f = bind binder ~f

    module Let_syntax = struct
      let return = return
      let map = Constraint.map
      let both = Constraint.both
      let bind = bind
    end
  end
end
