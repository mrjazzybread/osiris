PWD := $(shell pwd)

.PHONY: all
all:
	@ opam switch osiris && eval $(opam env)
# Build the Osiris translator.
	@ make --no-print-directory -C osiris
# Compile the OCaml source code of the OCaml standard library.
	@ cd coq-osiris/theories/stdlib/src && dune build .
# Compile the OCaml source code of our examples.
	@ cd coq-osiris/examples/src && dune build .
# Apply the Osiris translator to all of the above OCaml source code.
# The mark [og_] stands for "Osiris-generated".
	@ (cd osiris && dune exec src/Main.exe -- \
	     --root $(PWD)/coq-osiris \
             --out $(PWD)/coq-osiris \
	     --mark og_ \
	     --no-warnings \
	     --decorate \
	     all \
	  )
# Copy the translated files to a place where dune and Coq will see them.
#	@ cd coq-osiris/theories/stdlib && mv src/*.v .  # TODO these files are not yet used
	@ cd coq-osiris/theories/stdlib && rm -f src/*.v # TODO so we just remove them
	@ cd coq-osiris/examples && mv src/*.v .
# Now compile all of the Coq code.
	@ opam switch coq-osiris && eval $(opam env)
	@ make --no-print-directory -C coq-osiris

.PHONY: clean
clean:
	@ git clean -fdX .

# [make init] creates an opam switch named [osiris]
# and installs the necessary libraries and tools in it.

# It also installs Alectryon.

# This command can take about 12 minutes of real time
# on a multi-core desktop machine.

# The version numbers listed below should be kept in sync
# with those found in the file coq-osiris/dune-project.

.PHONY: init
init:
	opam switch create osiris 5.1.1+effect-syntax
	opam pin --switch=osiris --yes dune 3.11.0
	opam install --switch=osiris --yes pprint ocaml-compiler-libs
	opam install --switch=osiris --yes "coq-serapi>=8.10.0+0.7.0"
	opam switch create coq-osiris 4.14.1
	opam repo --switch=coq-osiris add coq-released https://coq.inria.fr/opam/released
	opam repo --switch=coq-osiris add iris-dev     git+https://gitlab.mpi-sws.org/iris/opam.git
	opam pin --switch=coq-osiris --yes dune 3.11.0
	opam pin --switch=coq-osiris --yes coq 8.17.1
	opam pin --switch=coq-osiris --yes coq-stdpp --dev-repo 1.9.0
	opam pin --switch=coq-osiris --yes coq-iris --dev-repo 4.1.0
	python3 -m pip install alectryon
