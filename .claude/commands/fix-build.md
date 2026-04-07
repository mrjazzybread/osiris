Repair all build errors introduced by recent local changes.

## Step 1 — Establish what changed

If the local changes are **not already visible in this conversation's context**,
retrieve them now:

- If there are staged changes: `git diff --staged`
- Otherwise, fall back to the most recent commit: `git diff HEAD~1`

Use this diff only to understand the scope of the change — which files were
touched and what was renamed, removed, or restructured — so you can anticipate
which callers are likely broken.

## Step 2 — Build

Run `make` from the repo root (this compiles the full pipeline: translator,
translations, and Rocq development).

If the build succeeds with no errors, report success and stop.

## Step 3 — Fix errors

For each compiler error:

1. Read the offending file at the reported line.
2. Understand why it is broken in light of the recent changes (renamed lemma,
   removed definition, changed signature, etc.).
3. Apply the minimal fix — update the call site to match the new name or
   interface. Do not refactor surrounding code.

Fix all errors from the current build output before re-running `make`.

## Step 4 — Repeat

Run `make` again. Repeat Steps 3–4 until the build is clean.

If the same error recurs after a fix attempt, re-examine the diff and the file
before trying again — do not apply the same incorrect fix twice.
