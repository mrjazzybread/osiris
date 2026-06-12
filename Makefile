PWD := $(shell pwd)

default: all

.PHONY: theory
theory:
	@ make --no-print-directory -C rocq-osiris core

.PHONY: translator
translator:
	@ make --no-print-directory -C osiris

.PHONY: all
all:
# Build the Osiris translator and the core Rocq theory.
	@ $(MAKE) --no-print-directory translator
	@ $(MAKE) --no-print-directory theory
# Compile the OCaml sources for the standard library and examples.
	@ make --no-print-directory -C rocq-osiris ocaml-libs
	@ dune build @examples/src/all --display=short
# Apply the Osiris translator to the standard library and examples.
	@ (cd osiris && dune exec src/Main.exe -- \
	     --root $(PWD) \
	     --out $(PWD) \
	     --mark og_ \
	     --no-warnings \
	     --decorate \
	     all \
	  )
# Copy the translated files to a place where dune and rocq will see them.
	@ cd rocq-osiris/stdlib && mv src/*.v .
	@ cd examples && mv src/*.v .
# Compile the stdlib and examples Rocq theories.
	@ make --no-print-directory -C rocq-osiris all
	@ dune build @examples/all --display=short

.PHONY: clean
clean:
	@ dune clean
	@ rm -f examples/og_*.v rocq-osiris/stdlib/og_*.v


# This is the desired version of OCaml.

OCAML_VERSION := 5.4.0
SWITCH_NAME ?= osiris

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
	$(PIN) rocq-core 9.1.0
	$(PIN) rocq-stdlib 9.1.0
	$(PIN) rocq-stdpp https://gitlab.mpi-sws.org/iris/stdpp.git#f5017975
	$(PIN) rocq-iris https://gitlab.mpi-sws.org/iris/iris.git#eea849e6
	$(PIN) rocq-equations 1.3.1+9.1
	$(PIN) ppx_sexp_conv v0.17.1
	$(PIN) ppx_deriving 6.1.1

.PHONY: create-mcp-json
create-mpc-json:
	@ $(file > .mcp.json, {"mcpServers": {"rocq-mcp": {"command": "$(PWD)/osirisvenv/bin/rocq-mcp","env": {"ROCQ_WORKSPACE": "$(PWD)"}}}})

# We leave it up to the user to install rocq-mcp into the osirisvenv virtual environment

.PHONY: install-rocq-mcp-deps
install-rocq-mcp:
	$(INSTALL) logs lwt coq-lsp
	python3 -m venv osirisvenv
	$(MAKE) create-mcp-json

.PHONY: emacs
emacs:
	$(INSTALL) tuareg merlin ocp-indent

.PHONY: vscode
vscode:
	$(INSTALL) vsrocq-language-server ocamlformat ocaml-lsp-server

.PHONY: runtests
runtests:
	@ cd interp && dune build
	@ cd tests && ./runtests.sh

.PHONY: check-axioms
check-axioms:
	@ cd rocq-osiris && ./check-axioms.sh
