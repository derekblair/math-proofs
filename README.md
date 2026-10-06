# Math Proofs

Machine-checked mathematics: each proven result ships as a **paper preprint**
(human-readable argument) paired with its **Lean 4 formalization**
(machine-checked proof). One directory per result under `papers/`; the Lean
project lives at the repo root.

Built with **Lean 4.34.1** + **Mathlib v4.34.1**. Every theorem typechecks with
`lake build`; each file lists its axiom dependencies explicitly.

## Results

### 1. A new Erdős–Straus covering identity — [PROVED]

For `n ≡ 217 (mod 264)`:

> `4/n = 1/((n+3)/4) + 1/(n(n+3)) + 1/(n(n+3)/11)`

Covers the prime **1009**, the smallest prime missed by the published
Mordell/Yamamoto/Rosati identities.

- Paper: [`papers/erdos-straus-identity-217mod264/`](papers/erdos-straus-identity-217mod264/) ([PDF](papers/erdos-straus-identity-217mod264/erdos-straus-identity-217mod264.pdf), [source](papers/erdos-straus-identity-217mod264/erdos-straus-identity-217mod264.tex))
- Lean: [`Mathproofs/ESIdentity.lean`](Mathproofs/ESIdentity.lean), theorem `es_identity_217mod264`
- Verification: typechecks cleanly, zero sorrys; `#print axioms` shows **only
  standard Lean axioms** (`propext`, `Classical.choice`, `Quot.sound`) — no
  extra assumptions. The 1009 worked example
  (`1/253 + 1/1021108 + 1/92828 = 4/1009`) is checked by `norm_num`.

### 2. A finite-identity barrier for Erdős–Straus on square classes mod 840 — [PROVED*]

No finite system of polynomial identities `4/(Aᵢt+Bᵢ) = Σ 1/Fᵢⱼ(t)` (positive
leading coefficients) can cover a full square class mod 840 — infinitely many
primes escape every such system. Witness: `p = 77,598,049 ≡ 529 (mod 840)`
lies in 0 of 30 candidate progressions.

- Paper: [`papers/erdos-straus-finite-identity-barrier/`](papers/erdos-straus-finite-identity-barrier/) ([PDF](papers/erdos-straus-finite-identity-barrier/erdos-straus-finite-identity-barrier.pdf), [source](papers/erdos-straus-finite-identity-barrier/erdos-straus-finite-identity-barrier.tex))
- Lean: [`Mathproofs/ESBarrier.lean`](Mathproofs/ESBarrier.lean), theorem `es_barrier`
- Verification: typechecks cleanly, zero sorrys, modulo **two labeled classical
  axioms**: `schinzel_mordell` (Schinzel 1956 / Mordell 1967 obstruction) and
  `dirichlet_arith_prog` (Dirichlet's theorem on arithmetic progressions —
  Mathlib 4.34.1 proves only the ≡1 mod k case). The CRT construction and
  escape argument are fully machine-checked.

## Building the Lean proofs

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain manager):

```bash
lake exe cache get   # fetch precompiled Mathlib oleans (large download)
lake build           # builds all of Mathproofs
```

CI (`.github/workflows/lean_action_ci.yml`) builds on every push via
`leanprover/lean-action`.

## Labeling convention

- **[PROVED]** — machine-checked by Lean, no extra axioms beyond Lean's standard ones.
- **[PROVED*]** — typechecks cleanly but depends on explicitly labeled classical-input
  axioms (named in the file and above); the labels say exactly what is assumed.
- Nothing here is claimed on the basis of a `sorry`.

## Adding a result

New results follow the same structure: `papers/<slug>/` gets the preprint
(`.tex` + compiled `.pdf`), `Mathproofs/<Name>.lean` gets the formalization
(imported from `Mathproofs.lean`), and this index gets a row. A result is only
promoted from [PROVED*] to [PROVED] when Lean checks it end to end.
