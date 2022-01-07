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
            Constraint.exists [ var, None ] t)
      }


    let forall () =
      { f =
          (fun k ->
            let var = Constraint.fresh () in
            let%map.Computation t = k var in
            Constraint.forall [ var ] t)
      }


    let exists_bindings bindings =
      { f =
          (fun k ->
            let%map.Computation t = k () in
            Constraint.exists bindings t)
      }


    let exists_vars vars = exists_bindings (List.map ~f:(fun x -> x, None) vars)

    let forall_vars vars =
      { f =
          (fun k ->
            let%map.Computation t = k () in
            Constraint.forall vars t)
      }


    let of_type type_ =
      { f =
          (fun k ->
            let bindings, var = Constraint.Shallow_type.of_type type_ in
            let%map.Computation t = k var in
            Constraint.exists bindings t)
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
    { universal_variables : variable list
    ; existential_bindings : Shallow_type.binding list
    ; term_bindings :
        (String.t, Constraint.variable, String.comparator_witness) Map.t
    ; local_constraint : Constraint.Rigid.t
    }

  let empty =
    { universal_variables = []
    ; existential_bindings = []
    ; term_bindings = Map.empty (module String)
    ; local_constraint = Rigid.true_
    }


  let merge t1 t2 =
    let exception Duplicate of string in
    try
      let term_bindings =
        Map.merge_skewed
          t1.term_bindings
          t2.term_bindings
          ~combine:(fun ~key _ _ -> raise (Duplicate key))
      in
      let universal_variables =
        t1.universal_variables @ t2.universal_variables
      in
      let existential_bindings =
        t1.existential_bindings @ t2.existential_bindings
      in
      let local_constraint =
        Rigid.conj t1.local_constraint t2.local_constraint
      in
      Ok
        { universal_variables
        ; existential_bindings
        ; term_bindings
        ; local_constraint
        }
    with
    | Duplicate term_var -> Error (`Duplicate_term_var term_var)


  let of_existential_bindings existential_bindings =
    { empty with existential_bindings }


  let of_term_binding x a =
    { empty with term_bindings = Map.singleton (module String) x a }


  let to_bindings t =
    ( t.universal_variables
    , t.existential_bindings
    , t.local_constraint
    , t.term_bindings |> Map.to_alist |> List.map ~f:(fun (x, a) -> x #= a) )
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

  let assert_ local_constraint = 
    write Fragment.{ empty with local_constraint }

  module Binder = struct
    include Computation

    let exists () =
      let var = Constraint.fresh () in
      let%bind.Computation () =
        write (Fragment.of_existential_bindings [ var, None ])
      in
      return var


    let forall () =
      let var = Constraint.fresh () in
      let%bind.Computation () = 
        write Fragment.{ empty with universal_variables = [ var ] }
      in
      return var

    let exists_bindings bindings =
      write (Fragment.of_existential_bindings bindings)


    let exists_vars vars = exists_bindings (List.map ~f:(fun x -> x, None) vars)

    let forall_vars vars =
      write Fragment.{ empty with universal_variables = vars }
      

    let of_type type_ =
      let bindings, var = Constraint.Shallow_type.of_type type_ in
      let%bind.Computation () =
        write (Fragment.of_existential_bindings bindings)
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
