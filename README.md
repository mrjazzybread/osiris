# Osiris

This is the artifact for the paper titled "Formal Semantics & Program Logics for a Fragment of OCaml".

## Project Overview

We provide an overview of the structure of the whole project in `ROADMAP.md`

## Compilation

### Dependencies

The project requires OCaml's package manager `opam`, and optionally the `ocamlwc` package.
On debian, these can be installed with
`sudo apt install opam ocamlwc`

Running `make init` then creates a new `opam` switch with all the required dependencies at
the right version.

The project depends on the opam libraries `ocaml`, `pprint`, `ocaml-compiler-libs`, `dune`, `coq`,
`iris`, `coq-equations`, and `std++`.

It is known to compile with the following versions of the packages:

| Package     | Version | Repo                                         |
|-------------|:-------:|:--------------------------------------------:|
| `ocaml`     | 5.3.0   | -                                            |
| `pprint`    | -       | -                                            |
| `ocaml-compiler-libs` | -  | -                                       |
| `dune`      | 3.17.2  | -                                            |
| `coq`       | 8.20.1  | https://coq.inria.fr/opam/released           |
| `coq-iris`  | 4.3.0   | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `coq-stdpp` | 1.11.0  | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `coq-equations` | 1.3.1+8.20 | -                                       |
| `ppx_sexp_conv` | v0.17.0 | -                                        |
| `ppx_deriving` | 6.0.3 | -                                           |

**If there is an error while the dependencies are being installed:**
It is recommended to update the list of opam packages with `opam update`,
and to continue installing with `make pin` to avoid creating a new switch.

For comfort, we also provide `make emacs` to install the dependencies necessary to use Emacs as an IDE for OCaml.

### Build

Running `make` will:
(1) build the translator,
(2) compile the example files in `coq-osiris/examples/src` and run the translator on them
(3) compile all coq files in the project.

For further details on running the translator manually, consult `osiris/osiris/README.md`.

## Validation

Running `make runtests` executes the validation tests for our semantics.

## Axioms

Running `make check-axioms` when the project is built will run `coqchk` and print out the axioms used in the coq development.
Note that the script filters out "uninteresting" actions, such as those found in `Coq.Floats.FloatAxioms`.
