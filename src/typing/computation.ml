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
    { t with substitution = Substitution.compose t.substitution substitution }
end

module Expression = struct
  type ('a, 'err) t = Input.t -> ('a, 'err) Result.t

  include Monad.Make2 (struct
    type nonrec ('a, 'err) t = ('a, 'err) t

    let return x _input = Ok x
    let bind t ~f input = Result.(t input >>= fun x -> f x input)
    let map = `Define_using_bind
  end)

  let of_result result _input = result
  let const x = return (Constraint.return x)
  let fail err : ('a, 'err) t = fun _input -> Error err
  let env : (Env.t, _) t = fun input -> Ok (Input.env input)

  let find_label ~label : (Types.label_declaration, _) t =
   fun input -> Env.find_label (Input.env input) ~label


  let find_constr ~name : (Types.constructor_declaration, _) t =
   fun input -> Env.find_constr (Input.env input) ~name


  let substitution : (Substitution.t, _) t =
   fun input -> Ok (Input.substitution input)


  let extend_substitution t ~substitution input =
    t (Input.extend_substitution input ~substitution)


  let find_var ~var : (Constraint.variable, _) t =
   fun input -> Substitution.find_var (Input.substitution input) ~var


  let run t ~env = t (Input.make ~env ~substitution:Substitution.empty)

  module Let_syntax = struct
    let return = return
    let ( >>| ) = Constraint.( >>| )
    let ( <*> ) = Constraint.( <*> )

    module Let_syntax = struct
      let return = return
      let map = Constraint.map
      let both = Constraint.both
      let bind = bind
    end
  end
end

include Expression

module Pattern = struct
  type 'a error =
    | Inj of 'a
    | Non_linear_pattern of string

  type ('a, 'err) t = (Fragment.t * 'a, 'err error) Expression.t

  include Monad.Make2 (struct
    type nonrec ('a, 'err) t = ('a, 'err) t

    let return x = Expression.return (Fragment.empty, x)

    let bind t ~f =
      let open Expression.Let_syntax in
      let%bind fragment1, x = t in
      let%bind fragment2, y = f x in
      Expression.of_result
        Result.(
          Fragment.merge fragment1 fragment2
          |> map_error ~f:(fun (`Non_linear_pattern x) -> Non_linear_pattern x)
          >>| fun fragment -> fragment, y)


    let map = `Define_using_bind
  end)

  let lift m : ('a, 'err) t =
   fun input ->
    Result.(
      m input |> map_error ~f:(fun x -> Inj x) >>| fun x -> Fragment.empty, x)


  let run t input =
    t input
    |> Result.map_error ~f:(function
           | Inj x -> x
           | Non_linear_pattern x -> `Non_linear_pattern x)


  let of_result result = lift (Expression.of_result result)
  let const x = lift (Expression.const x)
  let fail err = lift (Expression.fail err)
  let env = lift Expression.env
  let find_label ~label = lift (Expression.find_label ~label)
  let find_constr ~name = lift (Expression.find_constr ~name)
  let substitution = lift Expression.substitution
  let find_var ~var = lift (Expression.find_var ~var)

  let extend_substitution t ~substitution input =
    t (Input.extend_substitution input ~substitution)


  let write fragment _input = Ok (fragment, ())

  module Let_syntax = struct
    let return = return
    let ( >>| ) = Constraint.( >>| )
    let ( <*> ) = Constraint.( <*> )

    module Let_syntax = struct
      let return = return
      let map = Constraint.map
      let both = Constraint.both
      let bind = bind
    end
  end
end
