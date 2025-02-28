# Supplementary Material for ICFP Submission "Formal Semantics and Program Logics for a Fragment of OCaml"

## Codebase overview

### Translator

The following is the count for lines of code (`osiris/src`) for the
OCaml-to-Gallina translator, written in OCaml.

The count is without comments, counted with `cloc` (`cloc --include-lang=OCaml`)

|                    | Total (without comments) |
|--------------------|-------------------------|
| translator (src/) | 1762 LOC                 |


### Mechanization

The following is the count for lines of code (`coq-osiris/theories`) for the
mechanization (specification and proofs), written in Rocq.

The count is without comments, counted with the `coqwc` tool.

| Component                        | Spec   | Proof  | Total (without comments) |
|----------------------------------|--------|--------|-------------------------|
| Base definitions (toplevel)      | 38     | 21     | 59                      |
| Language definition (lang/)      | 869    | 261    | 1130                    |
| Semantics (semantics/)           | 2850   | 1036   | 3886                    |
| Program logic (program_logic/)   | 3704   | 3715   | 7419                    |
| Proof mode (proofmode/)          | 1822   | 250    | 2072                    |
| Logic-related utility (logic/)   | 215    | 263    | 478                     |
| Testing harness (test/)          | 806    | 442    | 1248                    |
| Integer library (CompCert/)      | 1953   | 3352   | 5305                    |
| Protocol library (Hazel/)        | 407    | 328    | 735                     |
| Stdlib (stdlib/)                 | 245    | 16     | 261                     |
| **Total**                        | 12909  | 9684   | **22593 LOC**           |


## Correspondence with the paper

### Section 3: A Monadic Interpreter

* OCaml expressions and patterns -> theories/lang/syntax.v
* Translator -> ../osiris
* OLang's type of values -> theories/lang/syntax.v
* eval_expr/eval_pat -> theories/semantics/eval.v
* internals of eval + other auxiliary functions -> theories/semantics/eval.v
* outcomes -> theories/semantics/outcome.v

### Section 4: The Micro Monad

* The micro public interface -> theories/semantics/code.v (and some bits in theories/semantics/micro.v)
* The micro monad definition -> theories/semantics/micro.v
* Codes -> theories/semantics/code.v

### Section 5: Small-step semantics for the Micro Monad

* Configurations/stores -> theories/semantics/step.v
* Stepping relation -> theories/semantics/step.v

### Section 6: Horus

* Pure reductions -> theories/semantics/pure.v
* Claims about pure steps -> theories/semantics/pure_step.v
* Pure wp -> theories/program_logic/pure/wp.v
* Pure rules for micro -> theories/program_logic/pure/pure_rules.v
* encoding -> theories/lang/encode.v
* Definition of pure__# (`pure` in the development) -> theories/program_logic/pure/judgements.v
* Definition of expr -> theories/program_logic/pure/judgements.v (just notation)
* Rules for expressions -> theories/program_logic/pure/expr_rules.v
* Definition of pat -> theories/program_logic/pure/pattern_rules.v
* Definition of branches -> theories/program_logic/pure/expr_rules.v
* Definition of spec -> theories/program_logic/pure/fun_spec.v
* Spec public API -> theories/program_logic/pure/fun_spec.v
* Merge example -> examples/proofs/merge.v
* Splay example -> examples/proofs/splay.v

### Section 7: Osiris

* Definition of impure -> theories/program_logic/ewp.v
* Micro level rules -> theories/program_logic/basic_rules.v
* Rules for Handle -> theories/program_logic/handler_rules.v
* Definition of impure__# -> theories/program_logic/ewp.v (lifting notation)
* Definition of deep-handler -> theories/program_logic/handler_rules.v

## Compilation

### Dependencies

The project depends on `ocaml`, `pprint`, `ocaml-compiler-libs`, `dune`, `coq`,
`iris`, `coq-equations`, and `std++`.

It is known to compile with the following versions of the packages:

| Package     | Version | Repo                                         |
|-------------|:-------:|:--------------------------------------------:|
| `ocaml`     | 5.3.0   | -                                            |
| `pprint`    | -       | -                                            |
| `ocaml-compiler-libs` | -  | -                                       |
| `dune`      | 3.17.2  | -                                            |
| `coq`       | 8.17.1  | https://coq.inria.fr/opam/released           |
| `coq-iris`  | dev     | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `coq-stdpp` | dev     | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `coq-equations` | 1.3+8.17 | -                                       |
| `ppx_sexp_conv` | v0.17.0 | -                                        |
| `ppx_deriving` | 6.0.3 | -                                           |
| `coq-serapi` | >=8.10.0+0.7.0 | -                                    |

*Notes*:
- `coq-serapi` is only necessary to build the (currently unmaintained) tutorial,
- you also need to install the python package `alectryon` to build the tutorial.


`make init` creates a new `opam` switch with all the required dependencies at
the right version.


### Build

Run `make`.

## Tutorial

The tutorial is not currently available.
