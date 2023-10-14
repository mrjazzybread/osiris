(lang dune 3.8)
(using coq 0.8)

(name osiris)

(generate_opam_files true)

(authors "François Pottier" "Armaël Guéneau" "Arnaud Daby-Seesaram")

(maintainers "François Pottier" "Armaël Guéneau" "Arnaud Daby-Seesaram")

(package
  (name osiris)
  (depends ocaml dune
  pprint compiler-libs
  coq-stdpp coq-iris
  coq-serapi))
