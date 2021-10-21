(lang dune 2.9)
(name dromedary)

(generate_opam_files true)

(license MIT)

(maintainers "ajo41@cam.ac.uk")

(authors "Alistair O'Brien")

(source
 (github johnyob/dromedary))

(package
 (name dromedary)
 (synopsis "An experimental subset of OCaml")
 (description
  "Dromedary is an experimental subset of OCaml, using constraint-based type inference!")
 (depends
  (ocaml
   (= 4.12.0))
  (dune
   (>= 2.9))))
