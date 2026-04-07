Fill an `admit` in a Rocq proof using the rocq-mcp interactive tools.

`$ARGUMENTS` should be a theorem name, or `file:theorem` if the name is ambiguous.

## Step 1 — Locate the admit

If a file is not specified, use Grep to find which `.v` file contains the theorem.

## Step 2 — Open the proof

Use `rocq_start(file=<file>, theorem=<theorem>, workspace="rocq-osiris")` to open
an interactive session and inspect the current proof goal at the admit.

## Step 3 — Search for relevant lemmas

Based on the goal, use `rocq_query` to find useful lemmas:
- `Search (<pattern>).` for lemmas matching a type shape
- `Check <name>.` to verify a candidate lemma's type
- `About <name>.` for a full summary

Search in context using `file=<file>` so all local definitions are in scope.

## Step 4 — Develop the proof interactively

Use `rocq_check(body=<tactics>)` to try tactics against the live proof state.
Iterate: inspect the goal after each step, search for more lemmas as needed,
try `rocq_step_multi` to explore several candidates at once.

Do not guess — read the goal carefully before choosing each tactic.

## Step 5 — Write back and validate

Once `rocq_check` reports `proof_finished=true`:
1. Replace the `admit` (and any placeholder tactics) in the `.v` file with the
   working proof from `proof_tactics`.
2. Run `dune build theories/path/to/file.vo` from `rocq-osiris/` to confirm the
   file compiles cleanly.
3. If the build fails, return to Step 2 with `rocq_start` to re-inspect.
