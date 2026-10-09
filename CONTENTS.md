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
  ([PDF](papers/r47-sat184-October-7-2026/sat184.pdf),
  [source](papers/r47-sat184-October-7-2026/sat184.tex),
  [build](papers/r47-sat184-October-7-2026/BUILD.md),
  [citation](papers/r47-sat184-October-7-2026/CITATION.bib))

## Versions and citations

Corrections and revisions are recorded as new versions, with previously
released versions remaining accessible in git history — see
[CHANGELOG.md](CHANGELOG.md). To cite an individual manuscript, use the
BibTeX block in its `papers/<slug>/CITATION.bib`.
