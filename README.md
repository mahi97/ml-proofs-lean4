# MLProofs: Verified AI/ML Proofs in Lean 4

**Mission:** Build a curated, reusable Lean 4 library that formalizes the core lemmas, assumptions, and flagship proofs used in AI/ML research—so authors can **port proofs** with confidence and reviewers can **check them mechanically**.

## Why this matters
- Reduce logical slips in papers (hidden assumptions, sloppy notation).
- Reuse a common base of theorems/inequalities across many papers.
- Make proofs executable artifacts (CI-verified) that accompany publications.

## Scope (v0 roadmap)
1. **Optimization (convex):** L-smoothness, μ-strong convexity, descent lemma, GD/SGD rates.
2. **Probability / Concentration:** Hoeffding, Bernstein, union bounds, sub-Gaussian basics.
3. **Learning Theory:** Finite-class PAC bounds, Rademacher (contraction), simple margin bounds.

> Longer term: stochastic & mirror descent, PAC-Bayes basics, matrix concentration, federated learning rates, selected paper “ports”.

## Design principles (non-negotiables)
- **Library-first:** reusable lemmas > one-off proofs.
- **Small modules, stable imports:** one public concept per file; no import cycles.
- **Doc & example for every public theorem.**
- **Deterministic builds:** pinned toolchain; CI must be green.
- **Semantic versioning:** clear upgrade notes per release.

## Repository layout
```

src/
MLProofs.lean
MLProofs/
Core/...
Optimization/...
Probability/...
LearningTheory/...
Catalog/...
examples/
test/
docs/

```

## Getting started
- Install Lean via `elan` and use `lake`.
- `lake exe cache get` to download mathlib caches.
- Open in VS Code (Lean 4 extension). See `CONTRIBUTING.md`.

## Audience
- Paper authors/reviewers in optimization, learning theory, and FL.
- Tool builders who want proof-checked appendices.

## License
MIT (see `LICENSE`).
