# Contributing

Thanks for helping build MLProofs! This project treats formal proofs as **public infrastructure**.
Please follow these rules so the library stays clean and fast.

## Workflow
1. **Fork**, create a feature branch: `feat/<area>-<short>`
2. Keep PRs **small and focused** (one module or lemma cluster).
3. Ensure **CI passes**: `lake build`, no lints, docs added.
4. Every public theorem/def has:
   - A **docstring** (plain English + notation),
   - **At least one example** in `examples/` *or* doctest snippet.

## Module & naming
- One public concept per file (≈200–800 lines).
- File path = module path. E.g. `src/MLProofs/Optimization/DescentLemma.lean`
- Namespaces: `MLProofs.Optimization` etc.
- Don’t create import cycles; keep DAG shallow.

## Simp & performance hygiene
- Prefer **local simp sets** in proofs; avoid growing global simp databases.
- Justify any `@[simp]` attribute in a docstring or comment.
- If a file slows dramatically (>2×), open an issue with a minimal repro.

## Tests & examples
- `test/` smoke tests for APIs and invariants.
- `examples/` short, pedagogical uses (import minimal umbrellas).
- Consider doctests inside docstrings for small facts.

## Documentation
- Start each file with a module header: purpose, main statements, dependencies.
- Paper ports (`Catalog/`) include citation + assumption mapping.

## Review policy
- Anything under `MLProofs.Core` requires review by a maintainer.
- Breaking changes: announce in PR title + add upgrade note in `CHANGELOG.md`.

## Coding style (Lean)
- Consistent names; prefer `camelCase` for lemmas/defs, `PascalCase` for modules.
- Short helper lemmas near their use; promote to `Core/` when reused.

## Releases
- **SemVer**: PATCH (docs/typos), MINOR (new modules/lemmas), MAJOR (breaking names).
