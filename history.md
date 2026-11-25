# History

For any withdrawn or superseded papers, their README files explain the gap and link to the historical manuscript. For any updated papers, previously released editions remain accessible in git history and through the version notes in their README. Corrections are disclosed here rather than buried.

## November 25, 2026

**Repository Restructure**

- Restructured the repository to mirror the `openai/math` layout (PR #45, `7f901baf`): moved the Lean project into [`lean/`](lean/) with discipline sub-libraries (`Mathproofs.NumberTheory`, `Mathproofs.Combinatorics`, `Mathproofs.Topology`, `Mathproofs.Dynamics`), upgraded [`lean/formalization.yaml`](lean/formalization.yaml) to v0.4 (`status.main_results`), added per-family scope docs ([`lean/docs/`](lean/docs/)), moved `papers/` to [`preprints/`](preprints/) (converting 13 mapped preprints to the OAI layout), rewrote [`CONTENTS.md`](CONTENTS.md) and [`README.md`](README.md), and renamed `CHANGELOG.md` to `history.md`. Post-scope Seam B / Seam C modules and preprints were preserved without invented remappings (D1); `LICENSE` (D3) and `overview.pdf` regeneration (D2) remain open items. All 102 moved non-root `.lean` files had `0` non-import diffs (`77` byte-identical, `25` import-path-only updates), intentionally retaining the 29 historical `Paper: papers/...` header comments in `lean/Mathproofs/NumberTheory/*.lean`.

**Verification & Provenance Corrections**

- **Full 114-module axiom audit:** PR #45's author-time `Lean.collectAxioms` sweep covered 96 of the 114 built `.olean` modules (`Mathproofs.*`, `MathProofs.*`, `SeamC.*`, omitting `Main` and `ComparatorChallenges.*`) and was overstated as "exhaustive" in the merged PR #45 description. Independent crossed review audited all **114/114** built `.olean`s: all **97/97** default-target modules (`Mathproofs` 79, `MathProofs` 12, `SeamC` 5, `Main` 1; `7,914` constants, `6,566` theorems) have `0` custom axioms and `0` disallowed violations (`0` `sorryAx`, `0` `ofReduceBool`, `0` `trustCompiler`), and all **17/17** non-default `ComparatorChallenges` modules (`194` constants, `90` theorems) have `0` custom axioms / `0` `ofReduceBool` / `0` `trustCompiler` and strictly the `39` deliberate `sorryAx` challenge placeholders.
- **`ComparatorChallenges` provenance:** [`lean/ComparatorChallenges/`](lean/ComparatorChallenges/) (17 `.lean` + 17 `.json` files, `39` deliberate `sorry` stubs covering 38 flagship theorems plus helper `Girth5Floor3v.scores_nonempty`) did not exist prior to PR #45 (`b2e4a11`) and was newly authored in commit `b2f02d4` by extracting standalone definitions and theorem signatures from `Mathproofs/` (not assembled from pre-existing challenge files). Dual-environment kernel `Expr` comparison verified exact statement and definition-body identity across all 17/17 pairs; running official `leanprover/comparator` on Lean 4.34.1 remains pending compatible toolchain binaries.
- **`*Statement.lean` census clarification:** The repository's **13** `*Statement.lean` files under `lean/` consist of **11** unbuilt `MathProofs/SeamB/*/Statement.lean` files (`70` pre-existing `sorry`s, excluded from default `lake build`) plus **2** built, sorry-free `SeamC/*/Statement.lean` files (`SeamC/A363166/Statement.lean`, `SeamC/A385590/Statement.lean`) — not 13 SeamB Statement files.
- **PR #45 follow-up hygiene fixes:** Replaced dangling `(see DISCREPANCY.md)` comments in `lean/lakefile.lean` and `lean/Mathproofs.lean`, added helper `Girth5Floor3v.scores_nonempty` to `lean/ComparatorChallenges/Girth5Extremal.json`, fixed the `## Labeling convention` heading hierarchy in `CONTENTS.md`, scoped `sorry_count: 0` in `lean/formalization.yaml` to the 97 default-built modules, and dated the historical October 6, 2026 restructure entry below.

## October 24, 2026

**Formalization Fix**

- *Absorption order and forcing spectrum* ([family 014](CONTENTS.md#family-014)). Repaired the vacuous global nonemptiness premise in `ESAbsorptionOrder`: `absorp_datum_iff` now assumes only `G.C.Nonempty`, while `rho_absorption_collapse` and `absorption_collapse_unique_core` assume only `H.C.Nonempty`. The new `datum_eq_of_absorpLE` proves the absorption-to-datum-equality direction without a nonemptiness premise.
- Repaired `singleton_factorization` by taking a finite ambient family `𝒢` with `S ⊆ 𝒢` and excluding singleton groups on `S0` only within `𝒢`. The former exclusion over every possible group forced `S0 = ∅`; the repaired hypothesis permits the census's nonempty set of cells.
- Updated the absorption manuscript and catalogue descriptions to state these hypotheses. The repaired statements retain `[PROVED]` status.

**Corrections**

- *An Erdős–Straus covering identity* ([family 001](CONTENTS.md#family-001)). Withdrew the claim that ES-001 is a new covering identity or that 1009 was missed by all previously published identities. Lopez (2024), [arXiv:2206.10319v4](https://arxiv.org/html/2206.10319v4), is prior art.
- Corrected the manuscript's title, abstract, literature discussion, example, conclusion, and bibliography, plus the README, catalogues, overview, citation metadata, and Lean commentary. The manuscript explains the specialization of Lopez's construction; the formal theorem statements are unchanged.
- The existing PDF remains a historical artifact containing the retracted claims. The corrected TeX source governs pending PDF regeneration.

## October 23, 2026

**Additional Formalizations**

This entry supersedes the remaining-boundary statements in the first-wave entry below where a bridge is now proved; that entry records its earlier state.

- Added CRT equivalences for actual unit residues congruent to 1 modulo 24 and their square subset modulo `24*∏p`, with `|Q|=|S|/2^k`. External filtered-frontier identification and cubic exclusion remain unproved.
- Added positive natural covering constructors and composed them with all three mod-7 families, T1 w=20 classes, and T2 q=7 fibers. Added branch-2 denominator algebra and (0,0)/(1,1) parent-progression coverage under explicit slope/intercept assumptions. External normalization and R74 certificates remain missing.
- Added exact unordered-edge accounting for feasible girth-5 replacement. Global extremality now implies the score ceiling, rigidity, and gap −1.
- Defined the explicit analytic gap factor, proved its logarithmic bridge, and proved its unique odd-block minimum under C22's quantitative bounds. Specialization to log₂3 continued fractions and Collatz dynamics remains.
- Proved the q-adic bounds available without R74, derived the redundant q∤m input, and checked a generic type-(0,1) counterexample to deleting R74. The fixed refined-target classification is still conditional.
- Kernel-checked all nine displayed one-hole Sidon rows, 183 blocked positions, their saturated ten-element extensions, and both C28 gate counterexamples. No search exhaustiveness or minimality claim is added.
- Proved the ES identity's exact six subclasses modulo 9240 and one-out-of-eleven residue count for every parent class, with positive covering witnesses.
- Registered all new modules in the full build and updated catalogues and manuscript sources. The historical-PDF policy remains in force.

**Formalization Fix**

- Removed `schinzel_mordell` and `dirichlet_arith_prog`: each former axiom admitted a contradiction. Withdrew the false rational-polynomial `es_barrier` statement. The replacement `es_crt_escape` proves escape from explicit local obstructions using Mathlib's general Dirichlet theorem. The integer-polynomial-to-obstruction implication remains unformalized; it is no longer advertised as a checked theorem.
- Added `es_covering_217mod264`, exporting positive natural denominators, exact denominator equations, and the Egyptian-fraction identity.
- Repaired `GapCF.c26c`: the quantitative K condition applies only when `rho < r`, and both strict equivalences are proved. Added C22 upper localization/argmin and C29 strict discrepancy, removed the unused C22 restriction, and included interval membership in the Delta argmin statement. The concrete Collatz gap specialization remains unassembled.
- Corrected girth-5 feasibility to require attachment containment, guards for candidate internal edges, and all internal-two-edge-path exclusions. Added regressions rejecting the review's invalid loop, triangle, four-cycle, and score-inflation moves. The score ceiling in rigidity remains explicit; graph extremality is not silently substituted for it. Added general triangle/four-cycle preservation and `emittedGraph`, which constructs a simple girth-at-least-five graph from every feasible move on a distinct triple, with all girth obligations proved from the local guards.
- Added `SidonSat184.r47_sat184`: a kernel proof of the nine-element witness, interval containment, Sidon property, and saturation. Corrected the paper: Astar contains 123, and all nine displayed one-hole sets have saturating ten-element extensions. Added the general extension theorem, a reproducible Python check, and the missing `strip.inc` figure source.
- Replaced all three refined-sieve `native_decide` calls with kernel proofs, removing their nonstandard certificate dependencies from all seven affected exported theorems.
- Aligned README, catalogues, overview, and affected manuscript sources with the proved statements. QR product counts, covering/descent kernels, and q-adic QQ/M23/R74 inputs retain explicit scope boundaries. Historical release claims below are records, not the current verification status.
- The missing Delta dependency at the original backlog publication was already fixed by `a26ba2c`; this correction does not claim that historical snapshot built successfully.
- Affected PDFs are historical pre-correction artifacts. No TeX toolchain was available, so corrected sources and build notes govern pending PDF regeneration. No rendered-PDF verification is claimed.

## October 11, 2026

**New Results Added**

- Published 29 Lean modules (28 `[PROVED]` + 1 `[PROVED*]` staged build dependency), all zero-sorry, machine-checked on bakkie (Lean 4.34.1 + Mathlib v4.34.1 pinned `d13f23b`):
  fiber-compatibility/suppression family (`ESFiberCompat`, `ESFiberCompatComposite`, `ESFiberTiling`, `CompositeSuppression`, `ESBranchTwo`), sieve/branch isolation (`ESRefinedSieveInverse` — `crt44_*` `[PROVED]`, three `native_decide` theorems `[PROVED*]` — `ESUBranchIsolation`), hole-suppression/absorption (`HoleSuppression`, `AbsorbedRegime`, `AbsorbedBound`), translation-march/dip family (`TranslationMarch`, `CorrectedMarch`, `TranslationMarchUnsat`, `HoleTwinDip`, `DipMarch`), sub-family/ladder (`ESSubfamilyExtended` — flagship `[PROVED]`, staged additions `[PROVED*]` — `MarchLadderCeiling`), transfer/overlap (`SigmaTrans`, `FiberOverlap`), locks/DAGs (`AbstractLock`, `TransDAG`), void/defect family (`VoidUnion`, `VoidLock`, `VoidMonoid`, `VoidDefectHom` `[PROVED]`; `VoidMonoidParam` `[PROVED*]` staged, build-clean, required build dependency of `VoidMonoid`/`VoidDefectHom`), ES absorption/forcing (`ESAbsorptionOrder`, `ESForcingSpectrum`, `ESForcingDecomp`).
- New manuscript families 007–015 in `CONTENTS.md` ([family 007](CONTENTS.md#family-007) through [family 015](CONTENTS.md#family-015)) with 9 preprints, each with a Formalization note cross-referencing module and theorem names.
- `Mathproofs.lean`: restored 4 published imports dropped from the working tree (`ESX0S1S3`, `ESDescentTransfer`, `CollatzGapHump`, `ESQadicBranch1`); every module registered exactly once.
- Excluded from this release: `AxProbe*` scratch (17 files), `ESCubicClassify.lean` (R89 quarantined), `DonorKernel.lean` (in flight, no dossier), `LadderTaxonomy`/`ConjectureFLemmas`/`PhaseSlip`/`MarchEndpoint` (`[PROVED*]`, staged-verification pending).
- Fixed stale `SS-001` paper links in `CONTENTS.md`; fixed `BUILD.md` directory paths in the three October papers.

## October 8, 2026

**New Results Added**

- Published 23 machine-checked Lean modules (`[PROVED]`, zero sorrys, standard axioms only): the Collatz gap-factor theory (`CollatzGapSinh`, `CollatzGapConvex`, `CollatzGapCF`, `CollatzGapC24`, `CollatzGapC24Lemma3`, `CollatzGapC23`, `CollatzGapC22C25`, `CollatzGapC29`, `CollatzGapC29Mirror`, `CollatzGapHump`), the Erdős–Straus witness-complex/QR-core theory (`WitnessComplexThm2`, `WitnessComplexThm13`, `ESPrimeSquareT2`, `EST1TwoCase`, `ESQRCore`, `ESQRCoreCount`, `ESFiveSevenForcing`, `ESMod7UniversalFamilies`, `ESX0S1S3`, `ESDescentTransfer`, `ESBranchSDREndgame`), the girth-5 3v floor theorem (`Girth5Floor3v`), and the q-adic branch-1 theorem (`ESQadicBranch1`).
- New manuscript families in `CONTENTS.md`: [002](CONTENTS.md#family-002) (Collatz convergent control), [003](CONTENTS.md#family-003) (ES witness-complex/QR-core), [004](CONTENTS.md#family-004) (girth-5), [005](CONTENTS.md#family-005) (q-adic), [006](CONTENTS.md#family-006) (saturated Sidon).
- New preprint: `r47-sat184-October-7-2026` (saturated 9-element Sidon set in `[1,184]`).
- Recorded every published theorem with its axiom status in the formalization catalogue.
- Excluded from this release: `ESCubicClassify.lean` (R89 quarantined, known breakage), `CollatzGapDelta.lean` (definitions only, no `[PROVED]` flagship), `DonorKernel.lean` / `ESRefinedSieveInverse.lean` / `ESUBBranchIsolation.lean` (verification ambiguous or in flight).

## Unreleased — Repository Restructure

**Fixes**

- Adopted a manuscript-map structure modeled on `openai/math`: per-manuscript directories with build and citation metadata, a root `CONTENTS.md` manuscript map, and per-theorem axiom status tracking.

## October 5, 2026

**New Results Added**

- Preprints release (`9ad4eb4`): published preprints alongside the Lean proofs with a structured README index pairing each paper with its Lean theorem and exact `[PROVED]`/`[PROVED*]` status.

## October 4, 2026

**New Results Added**

- Initial public release (`49b8c20`): Lean 4.34.1 formalizations `ESIdentity.lean` (`[PROVED]`, standard axioms only) and `ESBarrier.lean` (`[PROVED*]`, two labeled classical-input axioms: `schinzel_mordell`, `dirichlet_arith_prog` — later removed in the October 23, 2026 formalization fix).
