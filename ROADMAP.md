# Repo Roadmap

The Osiris project is organized as a dune workspace with four top-level sub-projects:
- `rocq-osiris/` — the core Rocq development (language model, program logics, stdlib translation)
- `interp/` — the validation framework (Rocq extraction + OCaml interpreter)
- `examples/` — translated OCaml examples and their Rocq proofs
- `osiris/` — the OCaml-to-Rocq translator

## Proofmode and Rocq Development

The Rocq development offers:
- a deep embedding of a fragment of OCaml in Rocq
- two program logics to reason about OCaml programs

### Model of the Language

- `rocq-osiris/theories/lang/`
  - `syntax.v` expressions, module expressions, values, patterns
  - `encode.v` the `Encode A` typeclass, which provides a function from `A -> val`
  - `type_nel.v` heterogeneous lists over encodable types

- `rocq-osiris/theories/semantics/`
  - `micro.v` defines the `micro` monad which models computations over expressions
  - `outcome.v` outcomes of computations: value returns, exception raises, and effect throws
  - `code.v` specializes the `stop` micro construct to OCaml
  - `eval.v` our monadic definitional interpreter with type `env -> expr -> micro val exc`
  - `step.v` operational semantics over the `micro` monad
  - `pure.v` a subset of pure reduction steps

### Proofmode

- `rocq-osiris/theories/program_logic/`
  - `thread_step.v` operational semantics from a "local" point of view, used by `ewp.v`
  - `ewp.v` the Iris instance over our language and operational semantics, and the effectful weakest precondition
  - `rules/` reasoning rules:
    - `basic_rules.v` core EWP definition and pure-step reasoning rules
    - `micro_rules.v` EWP rules over the micro monad constructs (ret, throw, crash, bind, try, Par)
    - `impure_rules.v` reasoning rules over impure/effectful combinators
    - `auxiliary_rules.v` reasoning rules for evaluating modules and struct items
    - `stop_rules.v` reasoning rules over the effects provided by `Stop`
    - `handler_rules.v` reasoning rules over handlers
    - `atomic_rules.v` `Atomic` typeclass instances for load/store/CAS and invariant-based atomic rules
    - `expr_rules.v` reasoning rules over evaluation of expressions
  - `fun_spec.v` `iSpec` abstraction for reasoning about n-ary function calls
  - `pure/` Horus (pure program logic):
    - `wp.v` the `pure_wp` definition, base definition for pure judgements
    - `judgements.v` the `pure` judgements and relevant notations
    - `pure_rules.v` reasoning rules over `pure` judgements
    - `expr_rules.v` reasoning rules about evaluation of expressions for pure judgements
    - `pattern_rules.v` reasoning rules about pattern matching
    - `toplevel_rules.v` reasoning rules about top-level definitions (struct items, bindings, modules)
    - `fun_spec.v` `Spec` abstraction for reasoning about n-ary function calls
  - `tactics.v` modality and mask tactics

- `rocq-osiris/theories/proofmode/`
  - `equality.v` a tactic to prove equality goals
  - `pure_tactics.v` tactics for proving pure goals
  - `handler_tactics.v` tactics to reason about handlers
  - `imp_tactics.v` tactics for proving Iris goals
  - `env_lookups.v` specifications for modules (environments) and the `imp_path` tactic
  - `setup.v` configuration for controlling opacity and general proofmode settings

- `rocq-osiris/theories/adequacy/`
  - `adequacy.v` adequacy theorem for Horus
  - `ewp_adequacy.v` adequacy theorem for Osiris (including closing over the gFunctors)

### Utility

- `rocq-osiris/theories/logic/` general utilities: ordering relations, properties of sorted lists, the empty type
  - `list_z.v` lists with indices in Z
  - `big_opLZ.v` big ops on lists with indices in Z
- `rocq-osiris/theories/CompCert/` a lifting of CompCert's treatment of integers
- `rocq-osiris/theories/Hazel/` a lifting of Hazel's notion of effect protocols
- `rocq-osiris/theories/base.v` basic imports, a few logical tautologies, a string destroying tactic
- `rocq-osiris/theories/test/` various manual tests for our operational semantics

### Standard Library

- `rocq-osiris/theories/stdlib/`
  - `Stdlib.v` translation-independent definitions of the OCaml standard library environment
  - `Externals.v` external (unverified) primitives
  - `og_*.v` auto-generated translations of OCaml stdlib modules (produced by the translator)
  - `src/` OCaml source files for the stdlib modules, compiled with `-bin-annot` to produce `.cmt` files for the translator
- `rocq-osiris/stdlib_proofs/` proofs about the translated standard library (depends on generated `og_*.v` files; built after translation, not part of `make theory`)
  - `array.v` specification and proof for array operations
  - `iarray.v` specification and proof for immutable array operations

### Examples

- `examples/`
  - `src/` OCaml source files for the examples, compiled with `-bin-annot`
  - `og_*.v` auto-generated translations of the example modules (produced by the translator)
  - `proofs/` specifications and proofs for the examples

## Validation

The interpreter for simulating our semantics is under `interp/`.

- `interp/`
  - `run.v` Rocq step function for the interpreter (`RunF` functor, I/O environment, string printers); compiled as the `osiris.interp` theory
  - `extracted/` receptacle for the extraction of the semantics from Rocq to OCaml; extraction commands are in `extract.v`
  - `translatorlib/` copies of translator source files (`Syntax.ml`, `Translate.ml`, etc.) used to convert OCaml ASTs into Osiris ASTs
  - `Read.ml` converts an OCaml file to an OCaml AST
  - `interp.ml` invokes the extracted `eval`, steps through the semantics, and intercepts I/O effects

The interpreter is the executable `interp.exe`. Run with e.g. `dune exec interp/interp.exe <file.ml>` from the workspace root.

Tests are in `tests/`:
- `tests/*.ml` handwritten `.ml` test files
- `tests/ocaml-testsuite/` tests adapted from OCaml's test suite
- `tests/runtests.sh` checks that for each test file, `ocaml file.ml` and `interp.exe file.ml` produce the same output

## Translator

The translator from OCaml source files to Rocq definitions is under `osiris/`.

- `osiris/src/`
  - `Syntax.ml` definition of the Osiris AST; must stay in sync with `rocq-osiris/theories/lang/syntax.v`
  - `Translate.ml` transforms OCaml parsetree expressions into the Osiris AST
  - `Rocqify.ml` transforms the Osiris AST into Rocq source text
  - `Main.ml` entry point; reads `.cmt` files, calls dune for module discovery, writes `og_*.v` files
  - `Dune.ml` discovers modules and `.cmt` file paths via `dune describe`; extracts workspace root for correct path resolution

## Build

The workspace uses a single `dune-workspace` at the root. Key make targets:

- `make translator` — build only the OCaml translator (`osiris/`)
- `make theory` — build core Rocq theory up to proofmode, excluding generated-file-dependent parts (`rocq-osiris/theories/`, but NOT `stdlib_proofs/` or `examples/`)
- `make` — full pipeline: translator → core theory → compile OCaml sources → run translator → move generated `.v` files → compile stdlib and examples Rocq theories
- `make clean` — `dune clean` + remove generated `og_*.v` files from `examples/` and `rocq-osiris/theories/stdlib/`

# Correspondence with the paper

We give a correspondence between features of the paper and their Rocq mechanization.

### Section 3: A Monadic Interpreter

* OCaml expressions and patterns → `rocq-osiris/theories/lang/syntax.v`
* Translator → `osiris/`
* OLang's type of values → `rocq-osiris/theories/lang/syntax.v`
* eval_expr/eval_pat → `rocq-osiris/theories/semantics/eval.v`
* internals of eval + other auxiliary functions → `rocq-osiris/theories/semantics/eval.v`
* outcomes → `rocq-osiris/theories/semantics/outcome.v`
* The micro public interface → `rocq-osiris/theories/semantics/code.v` (and some bits in `micro.v`)

### Section 4: The Micro Monad

* The micro monad definition → `rocq-osiris/theories/semantics/micro.v`
* Codes/system calls → `rocq-osiris/theories/semantics/code.v`

### Section 5: Small-step semantics for the Micro Monad

* Configurations/stores → `rocq-osiris/theories/semantics/step.v`
* Stepping relation → `rocq-osiris/theories/semantics/step.v`

### Section 6: Validation

* Extraction → `interp/extracted/extract.v`
* Step function → `interp/run.v`
* OCaml interpreter → `interp/interp.ml`
* Test suite → `tests/`

### Section 7: Horus

* Pure reductions → `rocq-osiris/theories/semantics/pure.v`
* Claims about pure steps → `rocq-osiris/theories/semantics/pure_step.v`
* Pure wp → `rocq-osiris/theories/program_logic/pure/wp.v`
* Pure rules for micro → `rocq-osiris/theories/program_logic/pure/pure_rules.v`
* encoding → `rocq-osiris/theories/lang/encode.v`
* Definition of pure__# (`pure` in the development) → `rocq-osiris/theories/program_logic/pure/judgements.v`
* Definition of expr → `rocq-osiris/theories/program_logic/pure/judgements.v` (just notation)
* Rules for expressions → `rocq-osiris/theories/program_logic/pure/expr_rules.v`
* Definition of pat → `rocq-osiris/theories/program_logic/pure/pattern_rules.v`
* Definition of branches → `rocq-osiris/theories/program_logic/pure/expr_rules.v`
* Definition of spec → `rocq-osiris/theories/program_logic/pure/fun_spec.v`
* Spec public API → `rocq-osiris/theories/program_logic/pure/fun_spec.v`
* Merge example → `examples/proofs/merge.v`
* Splay example → `examples/proofs/splay.v`

### Section 8: Osiris

* Definition of impure → `rocq-osiris/theories/program_logic/ewp.v`
* Micro level rules → `rocq-osiris/theories/program_logic/rules/micro_rules.v`
* Rules for Handle → `rocq-osiris/theories/program_logic/rules/handler_rules.v`
* Definition of impure__# → `rocq-osiris/theories/program_logic/ewp.v` (lifting notation)
* Find example → `examples/proofs/find.v`
