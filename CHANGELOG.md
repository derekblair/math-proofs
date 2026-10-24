# Changelog

Corrections and revisions are recorded as new versions; previously released
versions remain accessible in git history. Corrections are disclosed here
rather than buried.

## 2026-10-24 — ES identity novelty retraction

- Withdrew the claim that ES-001 is a new covering identity or that 1009 was
  missed by all previously published identities. Lopez (2024),
  [arXiv:2206.10319v4](https://arxiv.org/html/2206.10319v4), is prior art.
- Corrected the manuscript's title, abstract, literature discussion, example,
  conclusion, and bibliography, plus the README, catalogues, overview, citation
  metadata, and Lean commentary. The manuscript explains the specialization
  of Lopez's construction; the formal theorem statements are unchanged.
- The existing PDF remains a historical artifact containing the retracted
  claims. The corrected TeX source governs pending PDF regeneration.

## 2026-10-23 — Wave 2: constructive bridges and finite census proofs

This entry supersedes the remaining-boundary statements in the first-wave
entry below where a bridge is now proved; that entry records its earlier state.

- Added CRT equivalences for actual unit residues congruent to 1 modulo 24
  and their square subset modulo `24*∏p`, with `|Q|=|S|/2^k`. External
  filtered-frontier identification and cubic exclusion remain unproved.
- Added positive natural covering constructors and composed them with all
  three mod-7 families, T1 w=20 classes, and T2 q=7 fibers. Added branch-2
  denominator algebra and (0,0)/(1,1) parent-progression coverage under
  explicit slope/intercept assumptions. External normalization and R74
  certificates remain missing.
- Added exact unordered-edge accounting for feasible girth-5 replacement.
  Global extremality now implies the score ceiling, rigidity, and gap −1.
- Defined the explicit analytic gap factor, proved its logarithmic bridge,
  and proved its unique odd-block minimum under C22's quantitative bounds.
  Specialization to log₂3 continued fractions and Collatz dynamics remains.
- Proved the q-adic bounds available without R74, derived the redundant
  q∤m input, and checked a generic type-(0,1) counterexample to deleting R74.
  The fixed refined-target classification is still conditional.
- Kernel-checked all nine displayed one-hole Sidon rows, 183 blocked
  positions, their saturated ten-element extensions, and both C28 gate
  counterexamples. No search exhaustiveness or minimality claim is added.
- Proved the ES identity's exact six subclasses modulo 9240 and one-out-of-
  eleven residue count for every parent class, with positive covering witnesses.
- Registered all new modules in the full build and updated catalogues and
  manuscript sources. The historical-PDF policy remains in force.

## 2026-10-23 — Statement, proof-trust, and publication corrections

- Removed `schinzel_mordell` and `dirichlet_arith_prog`: each former axiom
  admitted a contradiction. Withdrew the false rational-polynomial
  `es_barrier` statement. The replacement `es_crt_escape` proves escape
  from explicit local obstructions using Mathlib's general Dirichlet
  theorem. The integer-polynomial-to-obstruction implication remains
  unformalized; it is no longer advertised as a checked theorem.
- Added `es_covering_217mod264`, exporting positive natural denominators,
  exact denominator equations, and the Egyptian-fraction identity.
- Repaired `GapCF.c26c`: the quantitative K condition applies only when
  `rho < r`, and both strict equivalences are proved. Added C22 upper
  localization/argmin and C29 strict discrepancy, removed the unused C22
  restriction, and included interval membership in the Delta argmin
  statement. The concrete Collatz gap specialization remains unassembled.
- Corrected girth-5 feasibility to require attachment containment, guards
  for candidate internal edges, and all internal-two-edge-path exclusions.
  Added regressions rejecting the review's invalid loop, triangle,
  four-cycle, and score-inflation moves. The score ceiling in rigidity
  remains explicit; graph extremality is not silently substituted for it.
  Added general triangle/four-cycle preservation and `emittedGraph`, which
  constructs a simple girth-at-least-five graph from every feasible move on
  a distinct triple, with all girth obligations proved from the local guards.
- Added `SidonSat184.r47_sat184`: a kernel proof of the nine-element
  witness, interval containment, Sidon property, and saturation. Corrected
  the paper: Astar contains 123, and all nine displayed one-hole sets have
  saturating ten-element extensions. Added the general extension theorem,
  a reproducible Python check, and the missing `strip.inc` figure source.
- Replaced all three refined-sieve `native_decide` calls with kernel
  proofs, removing their nonstandard certificate dependencies from all
  seven affected exported theorems.
- Aligned README, catalogues, overview, and affected manuscript sources
  with the proved statements. QR product counts, covering/descent kernels,
  and q-adic QQ/M23/R74 inputs retain explicit scope boundaries. Historical
  release claims below are records, not the current verification status.
- The missing Delta dependency at the original backlog publication was
  already fixed by `a26ba2c`; this correction does not claim that historical
  snapshot built successfully.
- Affected PDFs are historical pre-correction artifacts. No TeX toolchain
  was available, so corrected sources and BUILD notes govern pending PDF
  regeneration. No rendered-PDF verification is claimed.

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
