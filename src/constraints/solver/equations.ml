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
include Equations_intf

module Make
    (Former : Type_former.S)
    (Metadata : Unifier.Metadata)
    (Unifier : Unifier.S
                 with type 'a former := 'a Former.t
                  and type metadata := Metadata.t) =
struct
  module U = Unifier

  module Equation = struct
    type t = U.Type.t * U.Type.t [@@deriving sexp_of]

    let ( =%= ) t1 t2 = t1, t2
  end

  type t = Equation.t list

  let empty = []


  let pp_type_explicit type_ =
    let rec pp_type_explicit type_ =
      match U.Type.get_structure type_ with
      | U.Type.Var { flexibility = _ } ->
        Sexp.Atom (Int.to_string (U.Type.id type_))
      | U.Type.Former former -> Former.sexp_of_t pp_type_explicit former
    in
    Caml.Format.printf "%s\n" (Sexp.to_string_mach (pp_type_explicit type_))


  let pp_type type_ =
    Caml.Format.printf
      "id = %d"
      (U.Type.id type_);
    (match U.Type.get_structure type_ with
    | Var { flexibility } ->
      Caml.Format.printf
        ", flexibility = %s"
        (Sexp.to_string_hum (U.Type.sexp_of_flexibility flexibility))
    | _ -> ());
    Caml.Format.printf "\n";
    pp_type_explicit type_

  let pp t = 
    if List.is_empty t then Caml.Format.printf "No equations!\n"
    else
    List.iter t ~f:(fun (t1, t2) ->
      Caml.Format.printf "Equation:\n";
      pp_type t1;
      pp_type t2
      )

  exception Inconsistent

  (* [add_equation t (t1 =. t2)] adds the solved form of the equation
       [t1 =. t2] to the environment [t]. 
       
       Warning! Assumes [t1 =. t2] is not cyclic
    *)
  let add_equation t (type1, type2) =
    (* Caml.Format.printf "Adding equation:\n";
    pp_type type1;
    pp_type type2; *)
    (* TODO: Implement fold2_exn for Former. Removes reference side-effect. *)
    let t = ref t in
    let rec loop t1 t2 =
      match U.Type.get_structure t1, U.Type.get_structure t2 with
      | Var { flexibility = Rigid }, _ | _, Var { flexibility = Rigid } ->
        t := (t1, t2) :: !t
      | Former former1, Former former2 ->
        Former.iter2_exn ~f:loop former1 former2
      | Var { flexibility = Flexible }, _ | _, Var { flexibility = Flexible } -> 
        raise_s [%message "Adding non-rigid equation!"]
    in
    (try loop type1 type2 with
    (* If we add an equation that implies [bool = int], then the equation is
         inconsistent *)
    | Former.Iter2 -> raise Inconsistent);
    !t


  let equivalence_class t type_ =
    List.fold_left t ~init:[ type_ ] ~f:(fun acc (type1, type2) ->
        if U.Type.id type1 = U.Type.id type_
        then type2 :: acc
        else if U.Type.id type2 = U.Type.id type_
        then type1 :: acc
        else acc)


  (* This is actually horrifying, but its a prototype ;) *)
  let rec eq_modulo t type1 type2 : bool =
    (* Caml.Format.printf "Types:\n";
    pp_type type1;
    pp_type type2; *)

    let class1 = equivalence_class t type1
    and class2 = equivalence_class t type2 in
    (* Caml.Format.printf "Class1:\n";
    List.iter class1 ~f:pp_type;
    Caml.Format.printf "Class2:\n";
    List.iter class2 ~f:pp_type; *)
    (* Again, relying on exceptions for control flow. Unncessary, use fold! *)
    let equiv t1 t2 : bool =
      if phys_equal t1 t2
      then true
      else
        let exception Not_equiv in
        try
          (match U.Type.get_structure t1, U.Type.get_structure t2 with
          | Var _, Var _ -> if not (phys_equal t1 t2) then raise Not_equiv
          | Former former1, Former former2 ->
            Former.iter2_exn
              ~f:(fun t1 t2 -> if not (eq_modulo t t1 t2) then raise Not_equiv)
              former1
              former2
          | _, _ -> raise Not_equiv);
          true
        with
        | Former.Iter2 | Not_equiv -> false
    in
    List.exists ~f:(List.mem ~equal:(fun t1 t2 -> U.Type.id t1 = U.Type.id t2) class1) class2
    || List.exists
         ~f:(fun t1 -> List.exists ~f:(fun t2 -> equiv t1 t2) class1)
         class2
end