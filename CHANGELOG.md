# Changelog

Corrections and revisions are recorded as new versions; previously released
versions remain accessible in git history. Corrections are disclosed here
rather than buried.

## 2026-10-11 — Weekly sweep: 29 modules, 9 preprints

- Published 29 Lean modules (28 [PROVED] + 1 [PROVED*] staged build
  dependency), all zero-sorry, machine-checked on bakkie (Lean 4.34.1 +
  Mathlib v4.34.1 pinned d13f23b):
  fiber-compatibility/suppression family (`ESFiberCompat`,
  `ESFiberCompatComposite`, `ESFiberTiling`, `CompositeSuppression`,
  `ESBranchTwo`), sieve/branch isolation (`ESRefinedSieveInverse` — crt44_*
  [PROVED], three `native_decide` theorems [PROVED*] — `ESUBranchIsolation`),
  hole-suppression/absorption (`HoleSuppression`, `AbsorbedRegime`,
  `AbsorbedBound`), translation-march/dip family (`TranslationMarch`,
  `CorrectedMarch`, `TranslationMarchUnsat`, `HoleTwinDip`, `DipMarch`),
  sub-family/ladder (`ESSubfamilyExtended` — flagship [PROVED], staged
  additions [PROVED*] — `MarchLadderCeiling`), transfer/overlap
  (`SigmaTrans`, `FiberOverlap`), locks/DAGs (`AbstractLock`, `TransDAG`),
  void/defect family (`VoidUnion`, `VoidLock`, `VoidMonoid`,
  `VoidDefectHom` [PROVED]; `VoidMonoidParam` [PROVED*] staged, build-clean,
  required build dependency of `VoidMonoid`/`VoidDefectHom`), ES
  absorption/forcing (`ESAbsorptionOrder`, `ESForcingSpectrum`,
  `ESForcingDecomp`).
- New manuscript families 007–015 in `CONTENTS.md` with 9 preprints, each
  with a Formalization note cross-referencing module + theorem names.
- `Mathproofs.lean`: restored 4 published imports dropped from the working
  tree (`ESX0S1S3`, `ESDescentTransfer`, `CollatzGapHump`, `ESQadicBranch1`);
  every module registered exactly once.
- Excluded from this release: `AxProbe*` scratch (17 files),
  `ESCubicClassify.lean` (R89 quarantined), `DonorKernel.lean` (in flight,
  no dossier), `LadderTaxonomy`/`ConjectureFLemmas`/`PhaseSlip`/
  `MarchEndpoint` ([PROVED*], staged-verification pending).
- Fixed stale `SS-001` paper links in `CONTENTS.md`; fixed `BUILD.md`
  directory paths in the three October papers.

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
- New preprint: `papers/r47-sat184-October-7-2026/` (saturated 9-element Sidon set in
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
