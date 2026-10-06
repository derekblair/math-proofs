# Math Proofs

Lean 4 formalizations of results from an ongoing computational mathematics program
(Erdős–Straus conjecture, Collatz thresholds, saturated Sidon sets).

Built with **Lean 4.34.1** + **Mathlib v4.34.1**. Every theorem in this repo
typechecks with `lake build`; files list their axiom dependencies explicitly.

## Theorems

| File | Statement | Status |
|------|-----------|--------|
| `Mathproofs/ESIdentity.lean` | `es_identity_217mod264`: for `n ≡ 217 (mod 264)`, `4/n = 1/((n+3)/4) + 1/(n(n+3)) + 1/(n(n+3)/11)` — a new Erdős–Straus covering identity reaching the prime 1009, the smallest prime missed by the published Mordell/Yamamoto/Rosati identities | **Checked**, standard Lean axioms only (`#print axioms` clean) |
| `Mathproofs/ESBarrier.lean` | `es_barrier`: no finite system of polynomial identities `4/(Aᵢt+Bᵢ) = Σ 1/Fᵢⱼ(t)` covers a full square class mod 840 — infinitely many witness primes escape every progression | **Checked modulo 2 labeled classical axioms**: `schinzel_mordell` (Schinzel 1956 / Mordell 1967 obstruction) and `dirichlet_arith_prog` (Dirichlet's theorem on arithmetic progressions; Mathlib 4.34.1 proves only the ≡1 mod k case) |

The 1009 worked example (`1/253 + 1/1021108 + 1/92828 = 4/1009`) is also
machine-checked (`norm_num`).

## Building

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain manager):

```bash
lake exe cache get   # fetch precompiled Mathlib oleans (large download)
lake build           # builds all of Mathproofs
```

CI (`.github/workflows/lean_action_ci.yml`) builds on every push via
`leanprover/lean-action`.

## Labeling convention

- `[PROVED]` — machine-checked by Lean, no extra axioms beyond Lean's standard ones.
- `[PROVED*]` — typechecks cleanly but depends on explicitly labeled classical-input
  axioms (named in the file); the labels say exactly what is assumed.
- Nothing here is claimed on the basis of a `sorry`.

## Provenance

The identities and proofs were discovered/proved computationally; the Lean files
are the machine-checked record.
