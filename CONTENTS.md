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
| 002 | Collatz convergent control | in progress — formalizations not yet published |

## Family 001 — Erdős–Straus identities and obstructions

### <a id="es-001"></a>ES-001 — A new Erdős–Straus covering identity — [PROVED]

For `n ≡ 217 (mod 264)`:

> `4/n = 1/((n+3)/4) + 1/(n(n+3)) + 1/(n(n+3)/11)`

Covers the prime **1009**, the smallest prime missed by the published
Mordell/Yamamoto/Rosati identities.

- Paper: [`papers/erdos-straus-identity-217mod264/`](papers/erdos-straus-identity-217mod264/)
  ([PDF](papers/erdos-straus-identity-217mod264/erdos-straus-identity-217mod264.pdf),
  [source](papers/erdos-straus-identity-217mod264/erdos-straus-identity-217mod264.tex),
  [build](papers/erdos-straus-identity-217mod264/BUILD.md),
  [citation](papers/erdos-straus-identity-217mod264/CITATION.bib))
- Lean: [`Mathproofs/ESIdentity.lean`](Mathproofs/ESIdentity.lean), theorem
  `es_identity_217mod264` — typechecks cleanly, zero sorrys, standard Lean
  axioms only (`propext`, `Classical.choice`, `Quot.sound`).

### <a id="es-002"></a>ES-002 — A finite-identity barrier for Erdős–Straus on square classes mod 840 — [PROVED*]

No finite system of polynomial identities `4/(Aᵢt+Bᵢ) = Σ 1/Fᵢⱼ(t)`
(positive leading coefficients) can cover a full square class mod 840 —
infinitely many primes escape every such system. Witness:
`p = 77,598,049 ≡ 529 (mod 840)` lies in 0 of 30 candidate progressions.

- Paper: [`papers/erdos-straus-finite-identity-barrier/`](papers/erdos-straus-finite-identity-barrier/)
  ([PDF](papers/erdos-straus-finite-identity-barrier/erdos-straus-finite-identity-barrier.pdf),
  [source](papers/erdos-straus-finite-identity-barrier/erdos-straus-finite-identity-barrier.tex),
  [build](papers/erdos-straus-finite-identity-barrier/BUILD.md),
  [citation](papers/erdos-straus-finite-identity-barrier/CITATION.bib))
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

## Versions and citations

Corrections and revisions are recorded as new versions, with previously
released versions remaining accessible in git history — see
[CHANGELOG.md](CHANGELOG.md). To cite an individual manuscript, use the
BibTeX block in its `papers/<slug>/CITATION.bib`.
