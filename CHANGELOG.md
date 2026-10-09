# Changelog

Corrections and revisions are recorded as new versions; previously released
versions remain accessible in git history. Corrections are disclosed here
rather than buried.

## 2026-10-08 — Lean backlog publication

- Published 23 machine-checked Lean modules ([PROVED], zero sorrys, standard
  axioms only): the Collatz gap-factor theory (`CollatzGapSinh`,
  `CollatzGapConvex`, `CollatzGapCF`, `CollatzGapC24`, `CollatzGapC24Lemma3`,
  `CollatzGapC23`, `CollatzGapC22C25`, `CollatzGapC29`, `CollatzGapC29Mirror`,
  `CollatzGapHump`), the Erdős–Straus witness-complex/QR-core theory
  (`WitnessComplexThm2`, `WitnessComplexThm13`, `ESPrimeSquareT2`,
  `EST1TwoCase`, `ESQRCore`, `ESQRCoreCount`, `ESFiveSevenForcing`,
  `ESMod7UniversalFamilies`, `ESX0S1S3`, `ESDescentTransfer`,
  `ESBranchSDREndgame`), the girth-5 3v floor theorem (`Girth5Floor3v`),
  and the q-adic branch-1 theorem (`ESQadicBranch1`).
- New manuscript families in `CONTENTS.md`: 002 (Collatz convergent
  control), 003 (ES witness-complex/QR-core), 004 (girth-5), 005 (q-adic),
  006 (saturated Sidon).
- New preprint: `papers/r47-sat184/` (saturated 9-element Sidon set in
  [1,184]).
- `FORMALIZATION_CATALOGUE.md` now lists every published theorem with its
  axiom status.
- Excluded from this release: `ESCubicClassify.lean` (R89 quarantined,
  known breakage), `CollatzGapDelta.lean` (definitions only, no [PROVED]
  flagship), `DonorKernel.lean` / `ESRefinedSieveInverse.lean` /
  `ESUBBranchIsolation.lean` (verification ambiguous or in flight).

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
