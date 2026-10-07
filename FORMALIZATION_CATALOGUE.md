# Formalization Catalogue

Every theorem formalized in this repository, its verification status, and its
axiom dependencies. Statuses mirror the labeling convention in
[CONTENTS.md](CONTENTS.md).

| Theorem | File | Status | Axioms beyond Lean's standard ones | Paper |
|---|---|---|---|---|
| `es_identity_217mod264` | [Mathproofs/ESIdentity.lean](Mathproofs/ESIdentity.lean) | [PROVED] | none | [ES-001](CONTENTS.md#es-001) |
| `es_barrier` | [Mathproofs/ESBarrier.lean](Mathproofs/ESBarrier.lean) | [PROVED*] | `schinzel_mordell`, `dirichlet_arith_prog` | [ES-002](CONTENTS.md#es-002) |

## Checking instructions

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain manager)
and Lean 4.34.1 + Mathlib v4.34.1 (pinned by `lean-toolchain` and
`lake-manifest.json`):

```bash
lake exe cache get   # fetch precompiled Mathlib oleans (large download)
lake build           # builds all of Mathproofs
```

CI (`.github/workflows/lean_action_ci.yml`) runs the full build on every push.
`#print axioms <theorem>` on any entry above reproduces the axiom column;
nothing here is claimed on the basis of a `sorry`.

## Formalizations in progress (not yet published)

The following local formalizations are still being worked through the
publication pipeline — they are **not** part of this release:

- Collatz convergent-control machinery (`CollatzGap*.lean`, `ESCubicClassify.lean`)
  — several theorems machine-checked, others still carry `sorry`s or await
  their preprints. They will be published here per-result as they complete.
