# Contents

Lean formalizations and research manuscripts. Named Lean statements are checked;
not every manuscript claim has an end-to-end formalization. Manuscripts are organized into families — each family
groups a principal result with companion arguments, consequences, or
alternative proofs.

Built with **Lean 4.34.1** + **Mathlib v4.34.1**. See
[FORMALIZATION_CATALOGUE.md](FORMALIZATION_CATALOGUE.md) for the per-theorem
verification status and axiom dependencies.

The corrected `.tex` sources govern the October 23 changes. The overview and
ES identity/barrier, r47, and sieve-inverse PDFs are historical pre-correction
artifacts pending regeneration; see their BUILD notes.

## Manuscript map

| Family | Subject | Manuscripts |
|---|---|---|
| 001 | Erdős–Straus identities and obstructions | [ES-001](#es-001), [ES-002](#es-002) |
| 002 | Collatz convergent control (gap-factor theory) | [CC-001](#cc-001) |
| 003 | Erdős–Straus witness-complex and QR-core theory | [ES-003](#es-003) |
| 004 | Girth-5 extremal graphs | [G5-001](#g5-001) |
| 005 | q-adic classification of Erdős–Straus witnesses | [QA-001](#qa-001) |
| 006 | Saturated Sidon sets | [SS-001](#ss-001) |
| 007 | Erdős–Straus fiber compatibility and suppression | [ES-004](#es-004) |
| 008 | Sidon hole suppression and absorption | [SS-002](#ss-002) |
| 009 | Translation marches and dip mechanics | [SS-003](#ss-003) |
| 010 | Sub-family dichotomy and ladder ceilings | [SS-004](#ss-004) |
| 011 | Sigma transfer and fiber overlap | [SS-005](#ss-005) |
| 012 | Abstract locks and transition DAGs | [SS-006](#ss-006) |
| 013 | Void frames and defect calculus | [SS-007](#ss-007) |
| 014 | ES absorption order and forcing spectrum | [ES-005](#es-005) |
| 015 | Sieve inversion and branch isolation | [ES-006](#es-006) |

## Family 001 — Erdős–Straus identities and obstructions

### <a id="es-001"></a>ES-001 — An Erdős–Straus covering identity — [PROVED]

For `n ≡ 217 (mod 264)`:

> `4/n = 1/((n+3)/4) + 1/(n(n+3)) + 1/(n(n+3)/11)`

Covers the prime **1009**. The novelty claim is withdrawn in light of
[Lopez (2024), arXiv:2206.10319v4](https://arxiv.org/html/2206.10319v4);
see the manuscript's prior-art correction. The exact six
covered subclasses modulo 9240 and the one-out-of-eleven residue count are
proved in [ESIdentityCRT.lean](Mathproofs/ESIdentityCRT.lean).

- Paper: [`papers/erdos-straus-identity-217mod264-October-3-2026/`](papers/erdos-straus-identity-217mod264-October-3-2026/)
  ([PDF](papers/erdos-straus-identity-217mod264-October-3-2026/erdos-straus-identity-217mod264-October-3-2026.pdf),
  [source](papers/erdos-straus-identity-217mod264-October-3-2026/erdos-straus-identity-217mod264-October-3-2026.tex),
  [build](papers/erdos-straus-identity-217mod264-October-3-2026/BUILD.md),
  [citation](papers/erdos-straus-identity-217mod264-October-3-2026/CITATION.bib))
- Lean: [`Mathproofs/ESIdentity.lean`](Mathproofs/ESIdentity.lean), theorem
  `es_covering_217mod264` — exports positive natural denominators and the
  identity; `es_identity_217mod264` retains the rational equality. Standard Lean
  axioms only (`propext`, `Classical.choice`, `Quot.sound`).

### <a id="es-002"></a>ES-002 — CRT escape from local quadratic obstructions modulo 840 — [PROVED]

The checked result is `es_crt_escape`: for progressions with `8∣Aᵢ`
and explicit odd-prime nonsquare or 2-adic residue obstructions, infinitely
many primes in each listed square class modulo 840 avoid every progression.
It uses the general Dirichlet theorem already proved in Mathlib, with no
custom axioms. The implication from integer polynomial identities to those
local obstructions remains unformalized; the full polynomial-identity barrier
is not claimed as a Lean theorem.

- Corrected paper source: [ES barrier](papers/erdos-straus-finite-identity-barrier-October-4-2026/erdos-straus-finite-identity-barrier-October-4-2026.tex).
- Lean: [ESBarrier.lean](Mathproofs/ESBarrier.lean), theorem `es_crt_escape`.

## Labeling convention

- **[PROVED]** — machine-checked by Lean, no extra axioms beyond Lean's standard ones.
- **[CONDITIONAL]** — the larger interpretation has explicit, unformalized inputs.
- **[PROVED*]** — staged publication status; the catalogue states the checked scope.
- Nothing here is claimed on the basis of a `sorry`.

## Family 002 — Collatz convergent control (gap-factor theory)

### <a id="cc-001"></a>CC-001 — Analytic/continued-fraction kernels and conditional gap selectors — [CONDITIONAL]

The Lean modules prove analytic and continued-fraction identities plus
conditional argmin assemblies. [CollatzGapFactor.lean](Mathproofs/CollatzGapFactor.lean)
now defines the explicit Q-ratio times power-of-two-ratio and proves its
logarithm and difference identities. Its unique odd-block minimum theorem
supplies the objective bridge and minimizer existence, retaining C22's
quantitative hypotheses. The log₂3/Collatz-dynamics specialization remains
unassembled:

- Complete-quotient API for irrationals (`CollatzGapCF.lean`): error formula,
  ratio identity, determinant identity.
- C24 tail-mirror selector + strict dichotomy (`CollatzGapC24.lean`,
  `CollatzGapC24Lemma3.lean`); C23 sinh estimates (`CollatzGapC23.lean`,
  `CollatzGapSinh.lean`); C22/C25/C26 assembly (`CollatzGapC22C25.lean`).
- C18b convexity and C26 margin-duality trichotomy
  (`CollatzGapConvex.lean`); C29 discrepancy dominance and its from-below
  mirror (`CollatzGapC29.lean`, `CollatzGapC29Mirror.lean`).
- Adjacent-difference and interval-argmin criteria (`CollatzGapDelta.lean`).
- C64/C64b hump-law identity kernel (`CollatzGapHump.lean`).

- Lean: [`Mathproofs/CollatzGapCF.lean`](Mathproofs/CollatzGapCF.lean),
  [`Mathproofs/CollatzGapC24.lean`](Mathproofs/CollatzGapC24.lean),
  [`Mathproofs/CollatzGapC24Lemma3.lean`](Mathproofs/CollatzGapC24Lemma3.lean),
  [`Mathproofs/CollatzGapC23.lean`](Mathproofs/CollatzGapC23.lean),
  [`Mathproofs/CollatzGapC22C25.lean`](Mathproofs/CollatzGapC22C25.lean),
  [`Mathproofs/CollatzGapDelta.lean`](Mathproofs/CollatzGapDelta.lean),
  [`Mathproofs/CollatzGapConvex.lean`](Mathproofs/CollatzGapConvex.lean),
  [`Mathproofs/CollatzGapSinh.lean`](Mathproofs/CollatzGapSinh.lean),
  [`Mathproofs/CollatzGapC29.lean`](Mathproofs/CollatzGapC29.lean),
  [`Mathproofs/CollatzGapC29Mirror.lean`](Mathproofs/CollatzGapC29Mirror.lean),
  [`Mathproofs/CollatzGapHump.lean`](Mathproofs/CollatzGapHump.lean) —
  all typecheck cleanly, zero sorrys, standard Lean axioms only.
- Paper: preprint in preparation.

## Family 003 — Erdős–Straus witness-complex and QR-core theory

### <a id="es-003"></a>ES-003 — Witness-complex and QR arithmetic kernels — [PROVED]

Checked witness-complex arithmetic, reciprocity obstructions, and residue-class
exclusions. The CRT construction now proves the QR ratio for actual unit residues
congruent to 1 modulo 24 and their square subset modulo `24*∏p`. It does not
identify a separately filtered external frontier. The three mod-7 families,
T1 w=20 classes, and T2 q=7 fibers now provide positive natural covering
witnesses via [ESCovering.lean](Mathproofs/ESCovering.lean). Cubic exclusion,
external coverage tables, and the R74 sweep are not proved.
[ESDescentCovering.lean](Mathproofs/ESDescentCovering.lean) supplies the remaining
branch-2 denominator algebra and constructs full parent-progression covering
from the (0,0) and (1,1) arithmetic transfer hypotheses. It does not derive
those normalizations for every externally classified identity:


- [`Mathproofs/WitnessComplexThm2.lean`](Mathproofs/WitnessComplexThm2.lean)
  (`b0_vacuity`, `fiber_collision_law`),
  [`Mathproofs/WitnessComplexThm13.lean`](Mathproofs/WitnessComplexThm13.lean)
  (Thm 1(a) + Thm 3),
  [`Mathproofs/ESPrimeSquareT2.lean`](Mathproofs/ESPrimeSquareT2.lean),
  [`Mathproofs/EST1TwoCase.lean`](Mathproofs/EST1TwoCase.lean),
  [`Mathproofs/ESQRCore.lean`](Mathproofs/ESQRCore.lean),
  [`Mathproofs/ESQRCoreCount.lean`](Mathproofs/ESQRCoreCount.lean),
  [`Mathproofs/ESFiveSevenForcing.lean`](Mathproofs/ESFiveSevenForcing.lean),
  [`Mathproofs/ESMod7UniversalFamilies.lean`](Mathproofs/ESMod7UniversalFamilies.lean),
  [`Mathproofs/ESX0S1S3.lean`](Mathproofs/ESX0S1S3.lean),
  [`Mathproofs/ESDescentTransfer.lean`](Mathproofs/ESDescentTransfer.lean),
  [`Mathproofs/ESBranchSDREndgame.lean`](Mathproofs/ESBranchSDREndgame.lean) —
  all typecheck cleanly, zero sorrys, standard Lean axioms only.
- Paper: preprint in preparation.

## Family 004 — Girth-5 extremal graphs

### <a id="g5-001"></a>G5-001 — The 3v floor theorem for girth-5 graphs — [PROVED]

Corrected local reattachment feasibility and the identity-score floor.
`emittedGraph` proves that every feasible move on a distinct triple emits a
simple graph with no triangle or four-cycle. The new
[Girth5Extremal.lean](Mathproofs/Girth5Extremal.lean) proves exact unordered-edge
accounting and derives the score ceiling from global edge maximality. It then
proves maximum feasible score equals D and the three-vertex gap equals −1.

- Lean: [`Mathproofs/Girth5Floor3v.lean`](Mathproofs/Girth5Floor3v.lean) —
  typechecks cleanly, zero sorrys, standard Lean axioms only.
- Regressions: [`Mathproofs/Girth5Floor3vRegression.lean`](Mathproofs/Girth5Floor3vRegression.lean),
  five invalid moves rejected and two identity moves accepted.
- Paper: preprint in preparation.

## Family 005 — q-adic classification of Erdős–Straus witnesses

### <a id="qa-001"></a>QA-001 — Conditional branch-1 q-adic type theorem — [CONDITIONAL]

The arithmetic classification kernel proves v_q(r) ≤ v_q(A) assuming the
explicit QQ/M23 inputs and R74 exclusion of descended bundles. Those inputs
are not discharged for refined targets in this repository.
[ESQadicBoundary.lean](Mathproofs/ESQadicBoundary.lean) separately proves
α≤1 and ρ≤1 without R74, derives q∤m from the M23 divisibility premise,
and verifies a generic type-(0,1) counterexample to removing R74. That
example is not a counterexample to the fixed refined-target claim.

- Lean: [`Mathproofs/ESQadicBranch1.lean`](Mathproofs/ESQadicBranch1.lean) —
  typechecks cleanly, zero sorrys, standard Lean axioms only.
- Paper: preprint in preparation.

## Family 006 — Saturated Sidon sets

### <a id="ss-001"></a>SS-001 — A saturated 9-element Sidon set in [1,184] — [PROVED]

The set {16, 62, 66, 74, 88, 104, 117, 122, 123} is Sidon and saturated in
[1,184], including cardinality, containment, unique unordered sums, and
nonextendibility: `SidonSat184.r47_sat184` in
[Mathproofs/SidonSat184.lean](Mathproofs/SidonSat184.lean), checked by Lean
using standard axioms only. [SidonSat184Census.lean](Mathproofs/SidonSat184Census.lean)
also verifies all nine displayed one-hole rows, their 183 blocked positions,
the saturated ten-element extensions, and the two C28 gate counterexamples.
Search exhaustiveness and minimality are not claimed.

- Paper: [`papers/r47-sat184-October-7-2026/`](papers/r47-sat184-October-7-2026/)
  ([PDF](papers/r47-sat184-October-7-2026/r47-sat184-October-7-2026.pdf),
  [source](papers/r47-sat184-October-7-2026/r47-sat184-October-7-2026.tex),
  [build](papers/r47-sat184-October-7-2026/BUILD.md),
  [citation](papers/r47-sat184-October-7-2026/CITATION.bib))

## Family 007 — Erdős–Straus fiber compatibility and suppression

### <a id="es-004"></a>ES-004 — Fiber-compatibility and composite suppression — [PROVED]

R185/R192/R193/R205/R207/R209 fiber-compatibility kernel, composite theorem, thinned-tiling catalogue, suppression theory, and branch-2 degeneracy.

- Paper: [`papers/fiber-compatibility-composite-suppression-October-11-2026/`](papers/fiber-compatibility-composite-suppression-October-11-2026/)
  ([PDF](papers/fiber-compatibility-composite-suppression-October-11-2026/fiber-compatibility-composite-suppression-October-11-2026.pdf),
  [source](papers/fiber-compatibility-composite-suppression-October-11-2026/build/fiber-compatibility-composite-suppression-October-11-2026.tex),
  [build](papers/fiber-compatibility-composite-suppression-October-11-2026/BUILD.md),
  [citation](papers/fiber-compatibility-composite-suppression-October-11-2026/CITATION.bib))
- Lean modules:
  [`Mathproofs/ESFiberCompat.lean`](Mathproofs/ESFiberCompat.lean)
  [`Mathproofs/ESFiberCompatComposite.lean`](Mathproofs/ESFiberCompatComposite.lean)
  [`Mathproofs/ESFiberTiling.lean`](Mathproofs/ESFiberTiling.lean)
  [`Mathproofs/CompositeSuppression.lean`](Mathproofs/CompositeSuppression.lean)
  [`Mathproofs/ESBranchTwo.lean`](Mathproofs/ESBranchTwo.lean)

## Family 008 — Sidon hole suppression and absorption

### <a id="ss-002"></a>SS-002 — Hole suppression and absorption — [PROVED]

R199/R200 hole-suppression finite-set lemmas, absorbed-regime arithmetic, and the corrected T4 absorbed bound.

- Paper: [`papers/hole-suppression-absorption-October-11-2026/`](papers/hole-suppression-absorption-October-11-2026/)
  ([PDF](papers/hole-suppression-absorption-October-11-2026/hole-suppression-absorption-October-11-2026.pdf),
  [source](papers/hole-suppression-absorption-October-11-2026/build/hole-suppression-absorption-October-11-2026.tex),
  [build](papers/hole-suppression-absorption-October-11-2026/BUILD.md),
  [citation](papers/hole-suppression-absorption-October-11-2026/CITATION.bib))
- Lean modules:
  [`Mathproofs/HoleSuppression.lean`](Mathproofs/HoleSuppression.lean)
  [`Mathproofs/AbsorbedRegime.lean`](Mathproofs/AbsorbedRegime.lean)
  [`Mathproofs/AbsorbedBound.lean`](Mathproofs/AbsorbedBound.lean)

## Family 009 — Translation marches and dip mechanics

### <a id="ss-003"></a>SS-003 — Translation marches and dip mechanics — [PROVED]

R227/R231/R233/R235/R247 translation-march core, corrected ψ-translate and unsaturated march, hole-twin dip theorem, and dip-march sliding-window mechanics.

- Paper: [`papers/translation-march-dip-October-11-2026/`](papers/translation-march-dip-October-11-2026/)
  ([PDF](papers/translation-march-dip-October-11-2026/translation-march-dip-October-11-2026.pdf),
  [source](papers/translation-march-dip-October-11-2026/build/translation-march-dip-October-11-2026.tex),
  [build](papers/translation-march-dip-October-11-2026/BUILD.md),
  [citation](papers/translation-march-dip-October-11-2026/CITATION.bib))
- Lean modules:
  [`Mathproofs/TranslationMarch.lean`](Mathproofs/TranslationMarch.lean)
  [`Mathproofs/CorrectedMarch.lean`](Mathproofs/CorrectedMarch.lean)
  [`Mathproofs/TranslationMarchUnsat.lean`](Mathproofs/TranslationMarchUnsat.lean)
  [`Mathproofs/HoleTwinDip.lean`](Mathproofs/HoleTwinDip.lean)
  [`Mathproofs/DipMarch.lean`](Mathproofs/DipMarch.lean)

## Family 010 — Sub-family dichotomy and ladder ceilings

### <a id="ss-004"></a>SS-004 — Sub-family dichotomy and ladder ceilings — [PROVED]

R245 generalized sub-family theorem (+ staged R253/R261/R265 extensions) and the R259/R263 ladder-length ceiling.

- Paper: [`papers/subfamily-ladder-ceiling-October-11-2026/`](papers/subfamily-ladder-ceiling-October-11-2026/)
  ([PDF](papers/subfamily-ladder-ceiling-October-11-2026/subfamily-ladder-ceiling-October-11-2026.pdf),
  [source](papers/subfamily-ladder-ceiling-October-11-2026/build/subfamily-ladder-ceiling-October-11-2026.tex),
  [build](papers/subfamily-ladder-ceiling-October-11-2026/BUILD.md),
  [citation](papers/subfamily-ladder-ceiling-October-11-2026/CITATION.bib))
- Lean modules:
  [`Mathproofs/ESSubfamilyExtended.lean`](Mathproofs/ESSubfamilyExtended.lean)
  [`Mathproofs/MarchLadderCeiling.lean`](Mathproofs/MarchLadderCeiling.lean)

## Family 011 — Sigma transfer and fiber overlap

### <a id="ss-005"></a>SS-005 — Sigma transfer and fiber overlap — [PROVED]

R275 σ-transfer ascent machinery and R277 fiber-overlap lemmas.

- Paper: [`papers/sigma-transfer-fiber-overlap-October-11-2026/`](papers/sigma-transfer-fiber-overlap-October-11-2026/)
  ([PDF](papers/sigma-transfer-fiber-overlap-October-11-2026/sigma-transfer-fiber-overlap-October-11-2026.pdf),
  [source](papers/sigma-transfer-fiber-overlap-October-11-2026/build/sigma-transfer-fiber-overlap-October-11-2026.tex),
  [build](papers/sigma-transfer-fiber-overlap-October-11-2026/BUILD.md),
  [citation](papers/sigma-transfer-fiber-overlap-October-11-2026/CITATION.bib))
- Lean modules:
  [`Mathproofs/SigmaTrans.lean`](Mathproofs/SigmaTrans.lean)
  [`Mathproofs/FiberOverlap.lean`](Mathproofs/FiberOverlap.lean)

## Family 012 — Abstract locks and transition DAGs

### <a id="ss-006"></a>SS-006 — Abstract locks and transition DAGs — [PROVED]

R280/R287 abstract lock theory (repaired) and R279/R288/R292 dual-ascent barrier + ascent-depth.

- Paper: [`papers/abstract-lock-transdag-October-11-2026/`](papers/abstract-lock-transdag-October-11-2026/)
  ([PDF](papers/abstract-lock-transdag-October-11-2026/abstract-lock-transdag-October-11-2026.pdf),
  [source](papers/abstract-lock-transdag-October-11-2026/build/abstract-lock-transdag-October-11-2026.tex),
  [build](papers/abstract-lock-transdag-October-11-2026/BUILD.md),
  [citation](papers/abstract-lock-transdag-October-11-2026/CITATION.bib))
- Lean modules:
  [`Mathproofs/AbstractLock.lean`](Mathproofs/AbstractLock.lean)
  [`Mathproofs/TransDAG.lean`](Mathproofs/TransDAG.lean)

## Family 013 — Void frames and defect calculus

### <a id="ss-007"></a>SS-007 — Void frames and defect calculus — [PROVED] (VoidMonoidParam [PROVED*] staged)

R283/R289/R291/R296/R299/R300/R303 void frames under union, void locks, the N′_W defect monoid, and defect homomorphisms.

- Paper: [`papers/void-frames-defect-October-11-2026/`](papers/void-frames-defect-October-11-2026/)
  ([PDF](papers/void-frames-defect-October-11-2026/void-frames-defect-October-11-2026.pdf),
  [source](papers/void-frames-defect-October-11-2026/build/void-frames-defect-October-11-2026.tex),
  [build](papers/void-frames-defect-October-11-2026/BUILD.md),
  [citation](papers/void-frames-defect-October-11-2026/CITATION.bib))
- Lean modules:
  [`Mathproofs/VoidUnion.lean`](Mathproofs/VoidUnion.lean)
  [`Mathproofs/VoidLock.lean`](Mathproofs/VoidLock.lean)
  [`Mathproofs/VoidMonoidParam.lean`](Mathproofs/VoidMonoidParam.lean)
  [`Mathproofs/VoidMonoid.lean`](Mathproofs/VoidMonoid.lean)
  [`Mathproofs/VoidDefectHom.lean`](Mathproofs/VoidDefectHom.lean)

## Family 014 — ES absorption order and forcing spectrum

### <a id="es-005"></a>ES-005 — Absorption order and forcing spectrum — [PROVED]

ES absorption poset + redundancy rank, forcing spectrum partition, and forcing decomposition theorems A–D.
The datum equivalence assumes `G.C.Nonempty`; absorption collapse and its
unique core assume `H.C.Nonempty`. Singleton factorization takes a finite
ambient family `𝒢 ⊇ S`, with no singleton group on a cell of `S0` within `𝒢`.

- Paper: [`papers/es-absorption-forcing-October-11-2026/`](papers/es-absorption-forcing-October-11-2026/)
  ([PDF](papers/es-absorption-forcing-October-11-2026/es-absorption-forcing-October-11-2026.pdf),
  [source](papers/es-absorption-forcing-October-11-2026/build/es-absorption-forcing-October-11-2026.tex),
  [build](papers/es-absorption-forcing-October-11-2026/BUILD.md),
  [citation](papers/es-absorption-forcing-October-11-2026/CITATION.bib))
- Lean modules:
  [`Mathproofs/ESAbsorptionOrder.lean`](Mathproofs/ESAbsorptionOrder.lean)
  [`Mathproofs/ESForcingSpectrum.lean`](Mathproofs/ESForcingSpectrum.lean)
  [`Mathproofs/ESForcingDecomp.lean`](Mathproofs/ESForcingDecomp.lean)

## Family 015 — Sieve inversion and branch isolation

### <a id="es-006"></a>ES-006 — Sieve inversion and branch isolation — [PROVED]

R169/R178 residue-algebra and finite mod-3960 inverse-closure proofs, and
R163/R174 conditional u-branch isolation. All refined-sieve finite checks
now use kernel proofs. General lift-fiber claims and external data provenance
are outside these theorem types; see the corrected manuscript's scope note.

- Paper: [`papers/sieve-inverse-branch-isolation-October-11-2026/`](papers/sieve-inverse-branch-isolation-October-11-2026/)
  ([PDF](papers/sieve-inverse-branch-isolation-October-11-2026/sieve-inverse-branch-isolation-October-11-2026.pdf),
  [source](papers/sieve-inverse-branch-isolation-October-11-2026/build/sieve-inverse-branch-isolation-October-11-2026.tex),
  [build](papers/sieve-inverse-branch-isolation-October-11-2026/BUILD.md),
  [citation](papers/sieve-inverse-branch-isolation-October-11-2026/CITATION.bib))
- Lean modules:
  [`Mathproofs/ESRefinedSieveInverse.lean`](Mathproofs/ESRefinedSieveInverse.lean)
  [`Mathproofs/ESUBranchIsolation.lean`](Mathproofs/ESUBranchIsolation.lean)

## Versions and citations

Corrections and revisions are recorded as new versions, with previously
released versions remaining accessible in git history — see
[CHANGELOG.md](CHANGELOG.md). To cite an individual manuscript, use the
BibTeX block in its `papers/<slug>/CITATION.bib`.
