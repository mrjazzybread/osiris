# Repo Roadmap

The Osiris project can broadly be divided into three parts:
- The Rocq development, which can be found under `osiris/coq-osiris`
- The validation framework, which can be found under `osirs/coq-osiris/inter`
- The translator, is under `osiris/osiris`

## Proofmode and Rocq Development

The Rocq development offers:
- a deep embedding of a fragment of OCaml in Rocq
- two program logics to reason about OCaml programs

### Model of the Language

- `osiris/coq-osiris/theories/lang`
  - `syntax.v` expressions, modules expressions, values, patterns.
  - `sugar.v` shorthand for specific expressions and values (e.g. `EPair e1 e2 := ETuple [e1; e2]`)
  - `encode.v` the `Encode A` typeclass, which provides a function from `A -> val`
  - `type_nel.v` heteregenous lists over encodable types

- `osiris/coq-osiris/theories/semantics`
  - `micro.v` defines the `micro` monad which models computations over expressions, `code.v` specializes the monad to some of OCaml's features
  - `outcome.v` outcomes of computations: value returns, exception raises, and effect throws
  - `code.v` specializes the `stop` micro construct to OCaml
  - `eval.v` our monadic definitional interpreter with type `env -> expr -> micro val exc`
  - `step.v` operational semantics over the `micro` monad
  - `pure.v` a subset of pure reduction steps
  - `simplification.v` confluent and pure reductions steps, the basis of symbolic execution (see `simp_tactics.v`)
  - `simp_tactics.v` the `simp` tactic, as well as old tactics such as `simp_specify`

### Proofmode

- `osiris/coq-osiris/theories/program_logic`
  - `orisis/coq-osiris/theories/program_logic/pure/`: Horus
    - `wp.v` the [pure_wp] definition, which is the base definition for pure judgements.
    - `judgements.v` the [pure] judgements, and relevant notations.
    - `pure_rules.v` reasoning rules over [pure] judgements.
    - `expr_rules.v` reasoning rules about evaluation of expressions for pure judgements
    - `pattern_rules.v` reasoning rules about pattern matching
    - `toplevel_rules.v` reasoning rules about top-level definitions, such as
       struct items, bindings, and modules.
    - `fun_spec.v` [Spec] abstraction for reasoning about n-ary function calls
    - `adequacy.v` An adequacy statement over the pure Hoare-style logic
  - `ewp.v` the Iris instance over our language and operational semantics, and the effectful weakest precondition
  - `basic_rules.v` reasoning rules over the effectful weakest precondition
  - `handler_rules.v` reasoning rules over handlers
  - `expr_rules.v` reasoning rules over evaluation of expressions
  - `adequacy.v` adequacy theorem that follows from Iris' built-in adequacy theorem over our operational semantics
  - `tactics.v` modality and mask tactics

- `osiris/coq-osiris/theoris/proofmode`
  - `equality.v` a tactic to prove equality goals
  - `pure_tactics.v` tactics that are meant to be used while proving pure goals
  - `ewp_tactics.v` tactics that are meant to be used while proving Iris goals
  - `notations.v` notations for goal pretty-printing
  - `setup.v` configuration for controlling opacity and general proofmode settings
  - `specifications.v` utility to define specifications of modules/functions (mostly unused)

### Utility

- `osiris/coq-osiris/theories/logic`
  general utilies, currently contains ordering relations, properties of sorted lists, the empty type
- `osiris/coq-osiris/theories/CompCert` a lifting of CompCert's treatment of integers
- `osiris/coq-osiris/theories/Hazel` a lifting of Hazel's notion of effect protocols
- `osiris/coq-osiris/theories/stdlib` a translation of OCaml's standard library
- `osiris/coq-osiris/base.v` basic imports, a few logical tautologies, a string destroying tactic
- `osiris/coq-osiris/test` various manual tests for our operational semantics

### Examples

- `osiris/coq-osiris/examples`
  - `src/` directory containing our examples' `.ml` source files
  - `proofs/` directory containing our examples' specifications and proofs
- `osiris/coq-osiris/tutorial/tutorial.v` a web-browser based tutorial for using Osiris (completely outdated)

## Validation

The interpreter for simulating our semantics is under `osiris/coq-osiris/interp`.

- `osiris/coq-osiris/interp/`
  + `extracted/` is the receptacle for the extraction of the semantics from Rocq to OCaml, the extraction commands are in `extract.v`
  + `Read.ml` converts an OCaml file to an OCaml AST
  + `translatorlib/` converts the OCaml AST into an Osiris AST (it is 'dune copy' of translator files)
  + `interp.ml` invokes the extracted version of `eval`, steps through the semantics, and intercepts input/output effects to make them actual input/output operations.

The interpreter is then an executable `interp.exe`. It can be run with e.g. `dune exec interp/interp.exe <file.ml>` inside `coq-osiris`.

Tests are in `tests`:
- `tests/*.ml` are handwritten `.ml` test files
- `tests/ocaml-testsuite/` contain tests adapted from OCaml's test suite.
- `tests/runtests.sh`, to be run inside `tests`, checks that for each test file, running `ocaml file.ml` and `./interp.exe file.ml` produces the same output.


## Translator

The translator from OCaml source files to Rocq definitions is under `osiris/osiris`.

- `osiris/osiris/README.md` explains how to use the translator
- `osiris/osiris/src`
  - `Syntax.ml` definition of the Osiris AST, should be in sync with `osiris/coq-osiris/theories/lang/syntax.v`
  - `Translate.ml` transforms OCaml parsetree expressions into the Osiris AST
  - `Coqify.ml` transforms the Osiris AST into the Rocq Osiris AST

# Correspondence with the paper

We give a correspondence between features the of the paper and their Rocq mechanization.

### Section 3: A Monadic Interpreter

* OCaml expressions and patterns -> theories/lang/syntax.v
* Translator -> ../osiris
* OLang's type of values -> theories/lang/syntax.v
* eval_expr/eval_pat -> theories/semantics/eval.v
* internals of eval + other auxiliary functions -> theories/semantics/eval.v
* outcomes -> theories/semantics/outcome.v
* The micro public interface -> theories/semantics/code.v (and some bits in theories/semantics/micro.v)

### Section 4: The Micro Monad

* The micro monad definition -> theories/semantics/micro.v
* Codes/system calls -> theories/semantics/code.v

### Section 5: Small-step semantics for the Micro Monad

* Configurations/stores -> theories/semantics/step.v
* Stepping relation -> theories/semantics/step.v

### Section 6: Validation

* Extraction -> theories/interp/extracted/extract.v
* OCaml interpreter -> theories/interp/interp.ml
* Test suite -> ../../tests/

### Section 7: Horus

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

### Section 8: Osiris

* Definition of impure -> theories/program_logic/ewp.v
* Micro level rules -> theories/program_logic/basic_rules.v
* Rules for Handle -> theories/program_logic/handler_rules.v
* Definition of impure__# -> theories/program_logic/ewp.v (lifting notation)
* Find example -> examples/proofs/find.v
