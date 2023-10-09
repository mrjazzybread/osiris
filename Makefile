# This prevents Coq from producing stack backtraces.
export OCAMLRUNPARAM=

.PHONY: all
all:
	@printf "\r%-80s\n" "Build test/ml"
	@ dune build test/ml --
	@printf "\r%-80s\n" "Build libs/ml"
	@ dune build libs/ml --
	@printf "\r%-80s\n" "Translating Stdlib."
	@ dune exec translator/bin/main.exe -- -in-dir libs/ml/Stdlib -out libs/coq/Stdlib -root . -mode dune
	@printf "\r%-80s\n" "Building Osiris"
	@ dune build
	@printf "\r%-80s\n" "Done."

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
	opam pin dune 3.11.0 --yes
	opam pin coq 8.17.1 --yes
	opam pin coq-stdpp --dev-repo --yes
	opam pin coq-iris --dev-repo --yes
	opam install pprint ocaml-compiler-libs --yes
	opam install "coq-serapi>=8.10.0+0.7.0" --yes
	python3 -m pip install alectryon
