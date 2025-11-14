# Style Guide (Lean 4)

## Files & namespaces
- File per concept; ≤ ~1000 lines.
- `namespace MLProofs.<Area>` … `end MLProofs.<Area>`

## Docstrings
Each public def/lemma:
- One-line summary in plain English.
- Formal statement sketch if helpful.
- Notes on assumptions & typical use.

## Imports
- Prefer umbrella imports inside modules (`…/All.lean`).
- No cyclic imports; keep a bottom-up dependency order per folder.

## Lemma naming
- Prefer descriptive names: `descent_lemma_Lsmooth`, `gd_rate_strong_convex`.
- Use suffixes `_of_…`, `_iff_…` when natural.
- Tag rewrite-safe lemmas with `@[simp]` **sparingly**.

## Simp sets & attributes
- Localize simp sets in proofs: `simp [S1, S2]` rather than global attributes.
- Avoid global `simp` for heavy statements.

## Examples
- Provide self-contained examples with `import MLProofs` or a specific `…All`.
- Keep examples short and runnable.

## Notation
- Use mathlib notation when available.
- Introduce local notation only when it materially clarifies a proof.
