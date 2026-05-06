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
	@ dune build stdlib/Stdlib.vo --display=short

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

# [make axioms] looks for suspicious keywords in the Rocq sources.

.PHONY: axioms
axioms:
	@ for word in Axiom Abort Admitted ; do \
	    git grep $${word} '*.v' || true ; \
	  done

# [make tutorial] builds the tutorial. This requires Alectryon.

.PHONY: tutorial
tutorial: all
	@ dune build tutorial/tutorial.html

# [make view] opens the tutorial.

.PHONY: view
view: tutorial
	@ if command -v open >/dev/null ; then \
	    open tutorial/tutorial.html ; \
	  else \
	    firefox tutorial/tutorial.html ; \
	  fi
