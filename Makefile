PWD := $(shell pwd)

.PHONY: all
all:

# Build the Osiris translator.
	@ make --no-print-directory -C osiris
# Compile the OCaml source code of the OCaml standard library.
	@ cd coq-osiris/theories/stdlib && rm -f src/*.v # TODO so we just remove them
	@ cd coq-osiris/examples && mv src/*.v .
# Now compile all of the Coq code.
	@ make --no-print-directory -C coq-osiris

.PHONY: clean

.PHONY: init
init:
	opam switch create osiris 4.14.1
	opam repo --switch=osiris add coq-released https://coq.inria.fr/opam/released
	opam repo --switch=osiris add iris-dev     git+https://gitlab.mpi-sws.org/iris/opam.git
	opam pin --switch=osiris --yes dune 3.11.0
	opam pin --switch=osiris --yes coq 8.17.1
	opam pin --switch=osiris --yes coq-stdpp --dev-repo 1.9.0
	opam pin --switch=osiris --yes coq-iris --dev-repo 4.1.0
	opam install --switch=osiris --yes pprint ocaml-compiler-libs
