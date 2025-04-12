(lang dune 3.11)
(package
  (name narya)
  (depends
    (ocaml
      (>= 5.2.0))
    dune
    zarith
    zarith_stubs_js
    uuseg
    bwd
    algaeff
    asai
    yuujinchou
    react
    lwt
    lambda-term
    fmlib
    fileutils
    pprint))
(generate_opam_files)
