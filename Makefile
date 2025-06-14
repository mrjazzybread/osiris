PWD := $(shell pwd)

.PHONY: all
all:
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
	@ make --no-print-directory -C coq-osiris

.PHONY: clean
clean:
	@ git clean -fdX .

# This is the desired version of OCaml.

OCAML_VERSION := 5.3.0
SWITCH_NAME = osiris

# [make init] creates an opam switch named [osiris]
# and invokes [make pin].

.PHONY: init
init:
	opam switch create $(SWITCH_NAME) $(OCAML_VERSION)
	$(MAKE) pin

# Short-hands for opam commands.

ADD     := opam repo add --switch=$(SWITCH_NAME) --yes
PIN     := opam pin      --switch=$(SWITCH_NAME) --yes
INSTALL := opam install  --switch=$(SWITCH_NAME) --yes

# [make upgrade] updates the OCaml compiler
# in the existing opam switch named [osiris]
# and invokes [make pin].

.PHONY: upgrade
upgrade:
	$(PIN) --update-invariant ocaml $(OCAML_VERSION)
	$(MAKE) pin

# [make pin] installs the packages listed below in the opam switch [osiris].

# It no longer installs Alectryon.

# This command can take about 12 minutes of real time
# on a multi-core desktop machine.

# The version numbers listed below should be kept in sync
# with those found in the files
# osiris/dune-project and
# coq-osiris/dune-project.

.PHONY: pin
pin:
	$(PIN) dune 3.17.2
	$(INSTALL) tuareg merlin ocp-indent # for comfort
	$(INSTALL) pprint ocaml-compiler-libs
	$(ADD) coq-released https://coq.inria.fr/opam/released
	$(ADD) iris-dev     git+https://gitlab.mpi-sws.org/iris/opam.git
	$(PIN) coq 8.20.1
	$(PIN) coq-stdpp 1.11.0
	$(PIN) coq-iris 4.3.0
	$(PIN) coq-equations 1.3.1+8.20
	$(PIN) ppx_sexp_conv v0.17.0
	$(PIN) ppx_deriving 6.0.3

.PHONY: runtests
runtests:
	@ cd tests && ./runtests.sh

.PHONY: check-axioms
check-axioms:
	@ make --no-print-directory -C coq-osiris
	@ cd coq-osiris && ./check-axioms.sh
