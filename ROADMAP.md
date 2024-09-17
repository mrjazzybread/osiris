# Repo Roadmap

## Proofmode and Rocq Development

The Rocq development can be found under `osiris/coq-osiris`

### Model of the Language

- `osiris/coq-osiris/theories/lang`
  - `syntax.v` expressions, modules expressions, values, patterns.
  - `sugar.v` shorthand for specific expressions and values (e.g. `EPair e1 e2 := ETuple [e1; e2]`)
  - `encode.v` the `Encode A` typeclass, which provides a function from `A -> val`

- `osiris/coq-osiris/theories/semantics`
  - `micro.v` defines the `micro` monad which models computations over expressions, `code.v` specializes the monad to some of OCaml's features
  - `outcome.v` outcomes of computations: value returns, exception raises, and effect throws
  - `code.v` specializes the `stop` micro construct to OCaml
  - `eval.v` our monadic definitional interpreter with type `env -> expr -> micro val exc`
  - `step.v` operational semantics over the `micro` monad
  - `pure.v` a subset of pure reduction steps
  - `simplification.v` confluent and pure reductions steps, the basis of symbolic execution (see `simp_tactics.v`)

### Proofmode

- `osiris/coq-osiris/theories/program_logic`
  - `orisis/coq-osiris/theories/program_logic/pure/`
    - `pure_wp.v` the pure judgment and weakest precondition
    - `pure_encode.v` predicate wrapper for postconditions over encodable types
    - `pure_hoare.v` pure reasoning rules over the micro monad
    - `pure_eval.v` pure reasoning rules over language expressions
    - `simp_tactics.v` the `simp` tactic, as well as old tactics such as `simp_specify`
    - `auxiliary_judgements.v` the `pattern` judgement, which wraps the `extend` function found in `eval.v`
  - `pat.v` reasoning rules and tactics for pattern matching
  - `ewp.v` the Iris instance over our language and operational semantics, and the effectful weakest precondition
  - `basic_rules.v`, `handler_rules.v` reasoning rules over the effectful weakest precondition
  - `adequacy.v` adequacy theorem that follows from Iris' built-in adequacy theorem over our operational semantics
  - `tactics.v` modality and mask tactics

- `osiris/coq-osiris/theoris/proofmode`
  - `equality.v` a tactic to prove equality goals
  - `pure_tactics.v` tactics that are meant to be used while proving pure goals
  - `expr_rules.v` effectful reasoning rules over language expressions
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

## Translator

The translator from OCaml source files to Rocq definitions is under `osiris/osiris`.

- `osiris/osiris/README.md` explains how to use the translator
- `osiris/osiris/src`
  - `Syntax.ml` definition of the Osiris AST, should be in sync with `osiris/coq-osiris/theories/lang/syntax.v`
  - `Translate.ml` transforms OCaml parsetree expressions into the Osiris AST
  - `Coqify.ml` transforms the Osiris AST into the Rocq Osiris AST
