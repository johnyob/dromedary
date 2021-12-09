open Base
open Types

type 'a map = (String.t, 'a, String.comparator_witness) Map.t

type t =
  { types : type_declaration map
  ; constrs : constructor_declaration map
  ; labels : label_declaration map
  }

let find_constr env constr = Map.find_exn env.constrs constr
let find_label env label = Map.find_exn env.labels label