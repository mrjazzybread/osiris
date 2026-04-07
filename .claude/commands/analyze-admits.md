Find all `admit` and `Admitted` in the Rocq development and summarize them.

## Step 1 — Collect admits

Search for admits in `rocq-osiris/theories/`:

```
Grep pattern="\\badmit\\b|Admitted" path="rocq-osiris/theories" glob="*.v" output_mode="content" context=3
```

## Step 2 — Group and summarize

Group results by file. For each file, list:
- The file path (relative to repo root)
- Each admit with its enclosing theorem/lemma name and the surrounding goal context if visible

## Step 3 — Report hotspots

Produce a summary table:

| File | # admits |
|------|----------|
| ...  | ...      |

Then list each admit in detail:
- **File**: path
- **Theorem**: name of the enclosing `Lemma`/`Theorem`/`Definition`
- **Context**: the 3 lines around the admit

Finish with a count of total admits across the development.
