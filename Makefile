# This prevents Coq from producing stack backtraces.
export OCAMLRUNPARAM=

.PHONY: all
all:
	@ dune build test/ml --
	@ dune build libs/ml --
	@ dune exec translator/bin/main.exe -- -in-dir libs/ml/Stdlib -out libs/coq/Stdlib -root . -mode dune
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
