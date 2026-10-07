# Changelog

Corrections and revisions are recorded as new versions; previously released
versions remain accessible in git history. Corrections are disclosed here
rather than buried.

## Unreleased — repository restructure

- Adopted a manuscript-map structure modeled on openai/math: per-manuscript
  directories with `BUILD.md` and `CITATION.bib`, a root `CONTENTS.md`
  manuscript map, and a `FORMALIZATION_CATALOGUE.md` with per-theorem axiom
  status.

## 2026-10-05 — preprints release (`9ad4eb4`)

- Published preprints alongside the Lean proofs: `papers/` + structured README
  index pairing each paper with its Lean theorem and exact
  [PROVED]/[PROVED*] status.

## 2026-10-04 — initial public release (`49b8c20`)

- Lean 4.34.1 formalizations: `Mathproofs/ESIdentity.lean` ([PROVED],
  standard axioms only) and `Mathproofs/ESBarrier.lean` ([PROVED*], two
  labeled classical-input axioms: `schinzel_mordell`, `dirichlet_arith_prog`).
