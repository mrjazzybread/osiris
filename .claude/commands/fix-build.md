Repair all build errors introduced by recent local changes.

## Step 1 — Establish what changed

If the local changes are **not already visible in this conversation's context**,
retrieve them now:

- If there are staged changes: `git diff --staged`
- Otherwise, fall back to the most recent commit: `git diff HEAD~1`

Use this diff only to understand the scope of the change — which files were
touched and what was renamed, removed, or restructured — so you can anticipate
which callers are likely broken.

## Step 2 — Choose the local build command

Pick the narrowest build command that covers the changed files:

- **Translator only** (`osiris/src/` changes): `make translator` from the repo root.
- **Rocq theory only** (`rocq-osiris/` changes): `make theory` from the repo root
  (equivalent to `dune build` inside `rocq-osiris/`).
- **Both** (changes to both, or generated `og_*.v` files need refreshing): `make`
  from the repo root (full pipeline).

Run that local command first. If the build succeeds with no errors, skip to Step 5.

## Step 3 — Fix errors

For each compiler error:

1. Read the offending file at the reported line.
2. Understand why it is broken in light of the recent changes (renamed lemma,
   removed definition, changed signature, etc.).
3. Apply the minimal fix — update the call site to match the new name or
   interface. Do not refactor surrounding code.

Fix all errors from the current build output before re-running.

## Step 4 — Repeat locally

Re-run the same local build command from Step 2. Repeat Steps 3–4 until it is
clean.

If the same error recurs after a fix attempt, re-examine the diff and the file
before trying again — do not apply the same incorrect fix twice.

## Step 5 — Full build verification

Once the local build is clean, run `make` from the repo root to verify the full
pipeline (translator → translations → Rocq theory) is clean end-to-end.
