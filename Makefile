# This prevents Coq from producing stack backtraces.
export OCAMLRUNPARAM=

.PHONY: all
all:
	@ dune build

.PHONY: clean
clean:
	@ git clean -fdX

.PHONY: axioms
axioms:
	@ for word in Axiom Abort Admitted ; do \
	    git grep $${word} '*.v' || true ; \
	  done

.PHONY: tutorial
tutorial: all
	@ dune build tutorial/tutorial.html
