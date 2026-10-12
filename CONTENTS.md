# Contents

Machine-checked mathematics: every result ships as a **paper preprint**
(human-readable argument) paired with its **Lean 4 formalization**
(machine-checked proof). Manuscripts are organized into families — each family
groups a principal result with companion arguments, consequences, or
alternative proofs.

Built with **Lean 4.34.1** + **Mathlib v4.34.1**. See
[FORMALIZATION_CATALOGUE.md](FORMALIZATION_CATALOGUE.md) for the per-theorem
verification status and axiom dependencies.

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

### <a id="es-001"></a>ES-001 — A new Erdős–Straus covering identity — [PROVED]

For `n ≡ 217 (mod 264)`:

> `4/n = 1/((n+3)/4) + 1/(n(n+3)) + 1/(n(n+3)/11)`

Covers the prime **1009**, the smallest prime missed by the published
Mordell/Yamamoto/Rosati identities.

- Paper: [`papers/erdos-straus-identity-217mod264-October-3-2026/`](papers/erdos-straus-identity-217mod264-October-3-2026/)
  ([PDF](papers/erdos-straus-identity-217mod264-October-3-2026/erdos-straus-identity-217mod264-October-3-2026.pdf),
  [source](papers/erdos-straus-identity-217mod264-October-3-2026/erdos-straus-identity-217mod264-October-3-2026.tex),
  [build](papers/erdos-straus-identity-217mod264-October-3-2026/BUILD.md),
  [citation](papers/erdos-straus-identity-217mod264-October-3-2026/CITATION.bib))
- Lean: [`Mathproofs/ESIdentity.lean`](Mathproofs/ESIdentity.lean), theorem
  `es_identity_217mod264` — typechecks cleanly, zero sorrys, standard Lean
  axioms only (`propext`, `Classical.choice`, `Quot.sound`).

### <a id="es-002"></a>ES-002 — A finite-identity barrier for Erdős–Straus on square classes mod 840 — [PROVED*]

No finite system of polynomial identities `4/(Aᵢt+Bᵢ) = Σ 1/Fᵢⱼ(t)`
(positive leading coefficients) can cover a full square class mod 840 —
infinitely many primes escape every such system. Witness:
`p = 77,598,049 ≡ 529 (mod 840)` lies in 0 of 30 candidate progressions.

- Paper: [`papers/erdos-straus-finite-identity-barrier-October-4-2026/`](papers/erdos-straus-finite-identity-barrier-October-4-2026/)
  ([PDF](papers/erdos-straus-finite-identity-barrier-October-4-2026/erdos-straus-finite-identity-barrier-October-4-2026.pdf),
  [source](papers/erdos-straus-finite-identity-barrier-October-4-2026/erdos-straus-finite-identity-barrier-October-4-2026.tex),
  [build](papers/erdos-straus-finite-identity-barrier-October-4-2026/BUILD.md),
  [citation](papers/erdos-straus-finite-identity-barrier-October-4-2026/CITATION.bib))
- Lean: [`Mathproofs/ESBarrier.lean`](Mathproofs/ESBarrier.lean), theorem
  `es_barrier` — typechecks cleanly, zero sorrys, modulo two explicitly
  labeled classical-input axioms: `schinzel_mordell` (Schinzel 1956 /
  Mordell 1967 obstruction) and `dirichlet_arith_prog` (Dirichlet's theorem
  on arithmetic progressions — Mathlib 4.34.1 proves only the ≡1 mod k case).

## Labeling convention

- **[PROVED]** — machine-checked by Lean, no extra axioms beyond Lean's standard ones.
- **[PROVED*]** — typechecks cleanly but depends on explicitly labeled
  classical-input axioms (named in the file and above); the labels say exactly
  what is assumed.
- Nothing here is claimed on the basis of a `sorry`.

## Family 002 — Collatz convergent control (gap-factor theory)

### <a id="cc-001"></a>CC-001 — The Collatz gap-factor theory: selector, duality, and hump laws — [PROVED]

A machine-checked theory of the gap factor G(t) on from-above blocks of
log₂3's continued fraction, developed across thirteen Lean modules:

- Complete-quotient API for irrationals (`CollatzGapCF.lean`): error formula,
  ratio identity, determinant identity.
- C24 tail-mirror selector + strict dichotomy (`CollatzGapC24.lean`,
  `CollatzGapC24Lemma3.lean`); C23 sinh estimates (`CollatzGapC23.lean`,
  `CollatzGapSinh.lean`); C22/C25/C26 assembly (`CollatzGapC22C25.lean`).
- C18b convexity and C26 margin-duality trichotomy
  (`CollatzGapConvex.lean`); C29 discrepancy dominance and its from-below
  mirror (`CollatzGapC29.lean`, `CollatzGapC29Mirror.lean`).
- C64/C64b hump-law identity kernel (`CollatzGapHump.lean`).

- Lean: [`Mathproofs/CollatzGapCF.lean`](Mathproofs/CollatzGapCF.lean),
  [`Mathproofs/CollatzGapC24.lean`](Mathproofs/CollatzGapC24.lean),
  [`Mathproofs/CollatzGapC24Lemma3.lean`](Mathproofs/CollatzGapC24Lemma3.lean),
  [`Mathproofs/CollatzGapC23.lean`](Mathproofs/CollatzGapC23.lean),
  [`Mathproofs/CollatzGapC22C25.lean`](Mathproofs/CollatzGapC22C25.lean),
  [`Mathproofs/CollatzGapConvex.lean`](Mathproofs/CollatzGapConvex.lean),
  [`Mathproofs/CollatzGapSinh.lean`](Mathproofs/CollatzGapSinh.lean),
  [`Mathproofs/CollatzGapC29.lean`](Mathproofs/CollatzGapC29.lean),
  [`Mathproofs/CollatzGapC29Mirror.lean`](Mathproofs/CollatzGapC29Mirror.lean),
  [`Mathproofs/CollatzGapHump.lean`](Mathproofs/CollatzGapHump.lean) —
  all typecheck cleanly, zero sorrys, standard Lean axioms only.
- Paper: preprint in preparation.

## Family 003 — Erdős–Straus witness-complex and QR-core theory

### <a id="es-003"></a>ES-003 — The witness complex, square obstructions, and the QR-core — [PROVED]

A machine-checked theory of Erdős–Straus covering families on refined
moduli: the witness complex W(M), T2 prime-square obstruction, T1 two-case
theorem, and the QR-core (the set of quadratic-residue classes missed by
both covering systems) with its exact count and the 5/7-forcing lemma:

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

The emitted-graph re-attachment model and cross-edge harmlessness argument:
no improving 3v move on the extremal graphs.

- Lean: [`Mathproofs/Girth5Floor3v.lean`](Mathproofs/Girth5Floor3v.lean) —
  typechecks cleanly, zero sorrys, standard Lean axioms only.
- Paper: preprint in preparation.

## Family 005 — q-adic classification of Erdős–Straus witnesses

### <a id="qa-001"></a>QA-001 — Branch-1 q-adic type theorem — [PROVED]

v_q(r) ≤ v_q(A) on refined targets: the first classification theorem for
the q-adic types of Erdős–Straus witnesses.

- Lean: [`Mathproofs/ESQadicBranch1.lean`](Mathproofs/ESQadicBranch1.lean) —
  typechecks cleanly, zero sorrys, standard Lean axioms only.
- Paper: preprint in preparation.

## Family 006 — Saturated Sidon sets

### <a id="ss-001"></a>SS-001 — A saturated 9-element Sidon set in [1,184] — [SOLVED]

The set {16, 62, 66, 74, 88, 104, 117, 122, 123} is Sidon and saturated in
[1,184] (verified on three independent code paths).

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

R169/R178 44-CRT sieve inversion and R163/R174 u-branch isolation.

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
