(lang dune 3.6)
(name baguette)
(generate_opam_files true)

(package
 (name baguette)
 (synopsis "A CP solver with VeriPB proof logging and higher-order explanations")
 (depends
  (ocaml (>= 5.0))
  (menhir (>= 20220210))))
