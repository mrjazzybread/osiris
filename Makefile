PWD := $(shell pwd)

.PHONY: all
all:
# Build the Osiris translator.
	@ make --no-print-directory -C osiris
# Compile the OCaml source code of the OCaml standard library.
	@ cd rocq-osiris/theories/stdlib/src && dune build .
# Compile the OCaml source code of our examples.
	@ cd rocq-osiris/examples/src && dune build .
# Apply the Osiris translator to all of the above OCaml source code.
# The mark [og_] stands for "Osiris-generated".
	@ (cd osiris && dune exec src/Main.exe -- \
	     --root $(PWD)/rocq-osiris/ \
	     --out $(PWD)/rocq-osiris/ \
	     --mark og_ \
	     --no-warnings \
	     --decorate \
	     all \
	  )
# Copy the translated files to a place where dune and rocq will see them.
#	@ cd rocq-osiris/theories/stdlib && mv src/*.v .  # TODO these files are not yet used
	@ cd rocq-osiris/theories/stdlib && rm -f src/*.v # TODO so we just remove them
	@ cd rocq-osiris/examples && mv src/*.v .
# Now compile all of the rocq code.
	@ make --no-print-directory -C rocq-osiris

.PHONY: clean
clean:
	@ git clean -fdX .

# This is the desired version of OCaml.

OCAML_VERSION := 5.4.0
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
# rocq-osiris/dune-project.

.PHONY: pin
pin:
	$(PIN) dune 3.21.0
	$(INSTALL) pprint ocaml-compiler-libs
	$(ADD) rocq-released https://rocq-prover.org/opam/released
	$(ADD) iris-dev     git+https://gitlab.mpi-sws.org/iris/opam.git
	$(PIN) rocq-prover 9.0.0
	$(PIN) rocq-stdpp https://gitlab.mpi-sws.org/iris/stdpp.git#f5017975
	$(PIN) rocq-iris https://gitlab.mpi-sws.org/iris/iris.git#eea849e6
	$(PIN) rocq-equations 1.3.1+9.1
	$(PIN) ppx_sexp_conv v0.17.1
	$(PIN) ppx_deriving 6.1.1

.PHONY: emacs
emacs:
	$(INSTALL) tuareg merlin ocp-indent

.PHONY: vscode
vscode:
	$(INSTALL) vsrocq-language-server ocamlformat ocaml-lsp-server

.PHONY: runtests
runtests:
	@ cd rocq-osiris/interp && dune build
	@ cd tests && ./runtests.sh

.PHONY: check-axioms
check-axioms:
	@ cd rocq-osiris && ./check-axioms.sh
