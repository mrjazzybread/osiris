# Osiris

The Osiris project is a mechanized semantics and a formal verification environment for the
[OCaml](https://ocaml.org/) programming language, implemented in the Rocq proof assistant.

The mechanized development is under `coq-osiris`,
and an automatic translator from OCaml programs to our Rocq embedding is in `osiris`.

An overview of the structure of the whole project can be found in `ROADMAP.md`

## Compilation

The project requires OCaml's package manager `opam`.

Running `make init` then creates a new `opam` switch with all the required dependencies at
the right version.

**If there is an error while the dependencies are being installed:**\
It is recommended to update the list of opam packages with `opam update`,
and to continue installing with `make pin` to avoid creating a new switch.

For comfort, we also provide `make emacs` to install the dependencies necessary to use Emacs as an IDE for OCaml.

### Build

Running `make` will:\
(1) build the translator,\
(2) compile the example files in `coq-osiris/examples/src` and run the translator on them,\
(3) compile all coq files in the project.

### Dependencies

The project depends on the opam libraries `ocaml`, `pprint`, `ocaml-compiler-libs`, `dune`, `coq`,
`iris`, `coq-equations`, and `std++`.

It is known to compile with the following versions of the packages:

| Package         | Version | Repo                                         |
|-----------------|:-------:|:--------------------------------------------:|
| `ocaml`         | 5.3.0   | -                                            |
| `pprint`        | -       | -                                            |
| `ocaml-compiler-libs` | - | -                                            |
| `dune`          | 3.21.0  | -                                            |
| `rocq`          | 9.0.0   | https://coq.inria.fr/opam/released           |
| `rocq-iris`     | dev     | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `rocq-stdpp`    | dev     | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `rocq-equations`| 1.3.1+9.1 | -                                         |
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

Running `make check-axioms` when the project is built will run `coqchk` and print out the axioms used in the coq development.
Note that the script filters out "uninteresting" actions, such as those found in `Coq.Floats.FloatAxioms`.

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
and the .ml files have been compiled with the `-bin-annot` flag (see `coq-osiris/examples/src/dune`).

For a working example, consider the files in
`coq-osiris/examples/src`.

If we want to specifically translate one file, we can run
```
osiris \
    --root <path-to-this-dir>/coq-osiris/ \
    --out <path-to-this-dir>/coq-osiris/ \
    Bst
```

This will create a `bst.v` file next to `coq-osiris/examples/src/bst.ml`.
Crucially, `<path-to-this-dir>` needs to be an absolute path, not a relative one.

For further details on running the translator, consult `osiris/README.md`.
