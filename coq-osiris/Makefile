# This prevents Coq from producing stack backtraces.
export OCAMLRUNPARAM=
# This is used to find the script alectryon-custom.
export PATH:=$(shell pwd)/tutorial/bin:$(PATH)

.PHONY: all
all:
	@ dune build --display=short

.PHONY: clean
clean:
	dune clean

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

# [make view] opens the tutorial.

.PHONY: view
view: tutorial
	@ if command -v open >/dev/null ; then \
	    open tutorial/tutorial.html ; \
	  else \
	    firefox tutorial/tutorial.html ; \
	  fi
