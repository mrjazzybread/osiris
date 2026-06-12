# This prevents Rocq from producing stack backtraces.
export OCAMLRUNPARAM=
# This is used to find the script alectryon-custom.
export PATH:=$(shell pwd)/tutorial/bin:$(PATH)

.PHONY: all
all:
	@ dune build --display=short

.PHONY: core
core:
	@ dune build theories/ --display=short

.PHONY: stdlib
stdlib:
	@ dune build stdlib/ --display=short

.PHONY: ocaml-libs
ocaml-libs:
	@ dune build @stdlib/src/all --display=short

.PHONY: clean
clean:
	dune clean

.PHONY: lint
lint:
	@ dune build rocq-osiris.opam
	@ opam lint rocq-osiris.opam