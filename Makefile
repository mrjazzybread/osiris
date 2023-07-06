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

# [make init] creates an opam switch named [osiris]
# with the necessary libraries and tools.

.PHONY: init
init:
	opam switch create osiris 4.14.1
	eval $(opam env --switch=osiris)
	opam repository add coq-released https://coq.inria.fr/opam/released
	opam repository add iris-dev     git+https://gitlab.mpi-sws.org/iris/opam.git
	opam pin dune 3.6.1 --yes
	opam pin coq 8.16.1 --yes
	opam pin coq-stdpp --dev-repo --yes
	opam pin coq-iris --dev-repo --yes
	opam install pprint ocaml-compiler-libs --yes
	opam install "coq-serapi>=8.10.0+0.7.0" --yes
	python3 -m pip install alectryon
