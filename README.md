# Osiris

The Osiris project is a mechanized semantics and a formal verification environment for the
[OCaml](https://ocaml.org/) programming language, implemented in the Rocq proof assistant.

The mechanized development is under `rocq-osiris`,
and an automatic translator from OCaml programs to our Rocq embedding is in `osiris`.

An overview of the structure of the whole project can be found in `ROADMAP.md`

## Getting started

### Prerequisites

OCaml's package manager [`opam`](https://opam.ocaml.org/) should be installed.

### Install dependencies

Running `make init` creates a new `opam` switch named `osiris` and installs
all project dependencies (Rocq, Iris, stdpp, …) at their pinned versions.

If the installation fails partway through, running `opam update` followed by
`make pin` retries within the existing switch instead of recreating it.

### Build

Running `make` executes the full build pipeline:\
(1) the translator is built (`osiris/`),\
(2) the core Rocq theory is compiled (`rocq-osiris/theories/`),\
(3) the translator is run on the standard library and examples,\
(4) the stdlib and examples Rocq theories are compiled.

For day-to-day iteration, one of the narrower targets listed in
[Build targets](#build-targets) below is preferable — `make theory` and
`make translator` are typically the right choice.

### Editor setup (optional)

For Emacs, `make emacs` installs `tuareg`, `merlin`, and `ocp-indent`.\
For VS Code, `make vscode` installs `ocamlformat`, `ocaml-lsp-server`, and `vsrocq-language-server`.

## Build targets

The Makefile exposes the following targets. The narrowest one that covers a
given set of changes is preferable for faster iteration; the full `make` is
only required for end-to-end verification.

| Target            | What it does                                                           |
|-------------------|------------------------------------------------------------------------|
| `make`            | Full pipeline: translator → translate examples & stdlib → compile Rocq → build the interpreter |
| `make translator` | Compile the OCaml translator only (`osiris/`)                          |
| `make theory`     | Compile the core Rocq theory only (`rocq-osiris/theories/`)            |
| `make clean`      | Remove `_build/` and generated `og_*.v` files                          |
| `make runtests`   | Run the semantics validation tests (see [Validation](#validation))     |
| `make check-axioms` | List axioms used in the Rocq development (see [Axioms](#axioms))     |

When working only on `.v` files, `make theory` is sufficient and significantly
faster than `make`. When working only on the translator, use `make translator`.

## Setup targets

These targets manage the opam switch and editor tooling. They are normally
only needed once.

| Target          | What it does                                                              |
|-----------------|---------------------------------------------------------------------------|
| `make init`     | Create the `osiris` opam switch and install all project dependencies      |
| `make pin`      | Install dependencies into the current switch (skip switch creation)       |
| `make upgrade`  | Update the OCaml compiler in the existing `osiris` switch and re-pin      |
| `make emacs`    | Install Emacs OCaml tooling (`tuareg`, `merlin`, `ocp-indent`)            |
| `make vscode`   | Install VS Code OCaml + Rocq tooling (`ocamlformat`, `ocaml-lsp-server`, `vsrocq-language-server`) |
| `make install-rocq-mcp` | Install the dependencies for the `rocq-mcp` MCP server            |

`make init`, `make pin`, and `make upgrade` all accept `SWITCH_NAME=<name>`
if you want to operate on a switch other than the default `osiris`.

## Dependencies

The project depends on the opam libraries `ocaml`, `pprint`, `ocaml-compiler-libs`, `dune`, `rocq`,
`iris`, `rocq-equations`, and `std++`.

It is known to compile with the following versions of the packages:

| Package         | Version | Repo                                         |
|-----------------|:-------:|:--------------------------------------------:|
| `ocaml`         | 5.5.0   | -                                            |
| `pprint`        | -       | -                                            |
| `ocaml-compiler-libs` | - | -                                            |
| `dune`          | 3.21.0  | -                                            |
| `rocq`          | 9.2.0   | https://rocq-prover.org/opam/released        |
| `rocq-iris`     | 4.5.0   | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `rocq-stdpp`    | dev     |                                              |
| `rocq-equations`| 1.3.2+9.2 | -                                         |
| `ppx_sexp_conv` | v0.17.1 | -                                        |
| `ppx_deriving`  | 6.1.1   | -                                           |

## Publications

Remy Seassau, Irene Yoon, Jean-Marie Madiot, Francois Pottier.
Formal Semantics and Program Logics for a Fragment of OCaml.
ACM ICFP 2025, August 2025.
[[Paper](https://dl.acm.org/doi/10.1145/3747509)] [[Artifact](https://zenodo.org/records/16327523)]

## Validation

Running `make runtests` executes the validation tests for our semantics.

## Axioms

Running `make check-axioms` when the project is built will run `rocqchk` and print out the axioms used in the rocq development.
Note that the script filters out "uninteresting" actions, such as those found in `Corelib.Floats.FloatAxioms`.

## Manually Running the Translator

By default, the translator is compiled into
`osiris/_build/default/src/Main.exe`;
it can also be registered into the current opam switch with `cd osiris && make pin`.

Then, running
```
osiris \
    --root <project directory> \
    --out <output directory> \
    all
```
will translate every .ml file in `<project directory>` into a .v file,
as long as the project directory contains a **root** `dune-project` file,
and the .ml files have been compiled with the `-bin-annot` flag (see `rocq-osiris/examples/src/dune`).

For a working example, consider the files in
`rocq-osiris/examples/src`.

If we want to specifically translate one file, we can run
```
osiris \
    --root <path-to-this-dir>/rocq-osiris/ \
    --out <path-to-this-dir>/rocq-osiris/ \
    Bst
```

This will create a `bst.v` file next to `rocq-osiris/examples/src/bst.ml`.
Crucially, `<path-to-this-dir>` needs to be an absolute path, not a relative one.

For further details on running the translator, consult `osiris/README.md`.
