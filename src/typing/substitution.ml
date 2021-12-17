open! Import

type t = (String.t, Constraint.variable, String.comparator_witness) Map.t

let empty = Map.empty (module String)

let find_var t ~var =
  Result.of_option (Map.find t var) ~error:(`Unbound_type_variable var)


let of_alist alist =
  match Map.of_alist (module String) alist with
  | `Ok t -> Ok t
  | `Duplicate_key key -> Error (`Duplicate_type_variable key)


let to_alist t = Map.to_alist t

let of_type_vars vars =
  of_alist (List.map ~f:(fun var -> var, Constraint.fresh ()) vars)


let type_vars t = Map.keys t
let constraint_vars t = to_alist t |> List.map ~f:snd
let compose t1 t2 = Map.merge_skewed t1 t2 ~combine:(fun ~key:_ _ a -> a)
