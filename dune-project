(lang dune 3.11)
(license GPL-3.0-or-later)
(authors "Michael Shulman <shulman@sandiego.edu>")
(maintainers "Michael Shulman <shulman@sandiego.edu>")
(source (github gwaithimirdain/narya))
(package
  (name narya)
  (synopsis "A proof assistant for higher-dimensional type theories")
  (depends
    (ocaml
      (>= 5.2.1))
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
    pprint
    ppx_blob))
(generate_opam_files)
