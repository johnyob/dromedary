(* Alias to avoid clash w/ [Parsing] from [Core] *)
module P = Parsing
include Core
module Parsing = P
include Parsing
