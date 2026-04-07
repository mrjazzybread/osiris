# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**Osiris** is a mechanized semantics and formal verification framework for OCaml, implemented in the Rocq proof assistant (formerly Coq). It enables formal verification of OCaml programs using Iris, a concurrent separation logic.

The repository has two main components:
- **`osiris/`** — An OCaml-to-Rocq translator that converts typed OCaml ASTs (`.cmt` files) into Rocq definitions.
- **`rocq-osiris/`** — The Rocq proof development: language semantics, program logics (Iris-based EWP + pure Horus), stdlib translations, and example proofs.

## Build Commands

```bash
cd rocq-osiris && dune build #Compile the rocq development
make             # Full build: translator → translate examples → compile Rocq
make -C osiris   # Build only the OCaml translator
make -C rocq-osiris  # Build only the Rocq development
```

The full build pipeline:
1. Compile the Osiris translator (OCaml/Dune)
2. Compile OCaml stdlib sources and example files with `-bin-annot` (generates `.cmt`)
3. Run Osiris on all `.cmt` files → generates `og_*.v` files ("og_" = "Osiris-generated")
4. Move generated `.v` files into `rocq-osiris/theories/stdlib/` and `rocq-osiris/examples/`
5. Compile all Rocq code via dune

## Architecture

### Translator (`osiris/src/`)

- **`Syntax.ml`** — Osiris AST (must stay in sync with `rocq-osiris/theories/lang/syntax.v`)
- **`Translate.ml`** — OCaml parsetree (from `.cmt`) → Osiris AST
- **`Rocqify.ml`** — Osiris AST → Rocq source text
- **`Main.ml`** — Entry point; reads `.cmt` files, calls dune for discovery, writes `.v` files
- **`Cut.ml`** — Breaks large recursive definition groups
- **`Dune.ml`** — Discovers modules and `.cmt` file paths via dune

### Rocq Development (`rocq-osiris/theories/`)

**`lang/`** — Language model
- `syntax.v` — Core AST (variables, values, expressions, module expressions, patterns `pat`/`cpat`)
- `encode.v` — `Encode A` typeclass: injections from OCaml types into verifiable values

**`semantics/`** — Operational semantics
- `micro.v` — The micro monad modeling effectful computations
- `eval.v` — Monadic definitional interpreter (`env → expr → micro val exc`)
- `step.v` — Small-step operational semantics over configurations and stores
- `pure.v` — Pure reduction steps (no effects)

**`program_logic/`** — Iris-based program logic
- `ewp.v` — Effectful Weakest Precondition (EWP); the main Iris instance
- `fun_spec.v` — `iSpec`: reasoning about n-ary function calls
- `rules/` — EWP reasoning rules: `basic_rules.v`, `expr_rules.v`, `impure_rules.v`, `stop_rules.v`, `handler_rules.v`, `array_rules.v`
- `pure/` — Pure program logic (Horus): `wp.v`, `expr_rules.v`, `fun_spec.v`, `pattern_rules.v`, `toplevel_rules.v`
- `tactics.v`, `proofmode/` — Tactics for automation (e.g., `imp_store_atomic`, `imp_arith`, `imp_if`)

**`adequacy/`** — Metatheory
- `adequacy.v` — Adequacy for Horus
- `ewp_adequacy.v` — Full adequacy including effects

**`stdlib/`** — Auto-translated OCaml standard library (`og_*.v` files) + proofs in `stdlib/proofs/`

**`examples/`** — Auto-translated OCaml examples (`og_*.v`) + specifications and proofs in `examples/proofs/`

**`interp/`** — Validation: extraction of Rocq semantics to OCaml + interpreter for testing

### Invariant: `Syntax.ml` ↔ `syntax.v`

The OCaml file `osiris/src/Syntax.ml` and the Rocq file `rocq-osiris/theories/lang/syntax.v` define the same AST in their respective languages. They must be kept in sync manually whenever the language is extended.

## Proof Development Notes

- EWP proofs live in `rocq-osiris/examples/proofs/` and use the `ewp` tactic infrastructure.
- Pure (non-effectful) proofs use the Horus logic in `program_logic/pure/`.
- `rocq-osiris/theories/program_logic/proofmode/` contains automation for common proof patterns (handler tactics, equality, environment lookups).
- The `iSpec`/`Spec` abstractions in `fun_spec.v` are how function specifications are stated and composed.

## Rocq MCP Tools

The `rocq-mcp` MCP server must be used for all Rocq proof work. Prefer these tools over shell commands at every step:

- `rocq_query` — search for lemmas (`Search ...`), check types (`Check ...`), print definitions (`Print ...`)
- `rocq_start` — open a proof session on a theorem or file position to inspect goals
- `rocq_check` — run tactics interactively against a live proof state (faster than recompiling)
- `rocq_step_multi` — try multiple tactic candidates at once
- `rocq_compile` / `rocq_compile_file` — batch-compile for final validation

## Proof Repair Workflow

When fixing broken proofs, follow this sequence:

1. `rocq_start(file=..., theorem=...)` — open the proof and inspect the goal
2. `rocq_check(body=...)` — develop tactics interactively
3. `rocq_query` — search for relevant lemmas as needed
4. Write the working proof back to the `.v` file
5. `dune build theories/path/to/file.vo` — validate the single file compiles
6. `dune build` (or `make -C rocq-osiris`) — verify the full Rocq development builds
7. `make` — run the full pipeline if translator or generated files were affected

## Instructions

Read files with purpose. Before reading a file, know what you're looking for. Use Grep to locate relevant sections before reading entire large files. Never re-read a file you've already read in this session. For files over 500 lines, use offset/limit to read only the relevant section.

The descriptions of all files are in ROADMAP.md, make sure that you actually need the information from a file before reading it.
