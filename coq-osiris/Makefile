# This prevents Coq from producing stack backtraces.
export OCAMLRUNPARAM=

.PHONY: all
all:
	@ dune build

.PHONY: clean
clean:
	@ git clean -fdX .

.PHONY: lint
lint:
	@ dune build coq-osiris.opam
	@ opam lint coq-osiris.opam

# [make axioms] looks for suspicious keywords in the Coq sources.
.PHONY: axioms
axioms:
	@ for word in Axiom Abort Admitted ; do \
	    git grep $${word} '*.v' || true ; \
	  done

# [make tutorial] builds the tutorial. This requires Alectryon.
.PHONY: tutorial
tutorial: all
	@ dune build tutorial/tutorial.html
