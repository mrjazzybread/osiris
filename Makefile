# This prevents Coq from producing stack backtraces.
export OCAMLRUNPARAM=

.PHONY: clean
clean::
	git clean -fX

-include Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

.PHONY: axioms
axioms:
	@ for word in Axiom Abort Admitted ; do \
	    echo "Looking for $${word}..." ; \
	    grep -w $${word} theories/*.v || true ; \
	  done

.PHONY: tutorial
tutorial: all
	alectryon -R . AmpleStep tutorial/tutorial.v
