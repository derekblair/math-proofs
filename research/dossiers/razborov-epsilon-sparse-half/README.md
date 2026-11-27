# Razborov's epsilon question for sparse halves

[Alexander Razborov, §5](https://arxiv.org/html/2104.09406v2#S5) asks whether the exact sparse-half bound extends below the independence threshold 2/5 by a fixed positive amount.

**Theorem.** There is an absolute real ε > 0 such that any triangle-free graph on n vertices with an independent set of size at least (2/5 − ε)n has a set of ⌊n/2⌋ vertices spanning at most n²/50 edges.

The end-to-end Lean statement is `SparseHalfGraphon.razborov_sparse_half_epsilon` in [graphon/RazborovEpsilon.lean](graphon/RazborovEpsilon.lean). The input is a loopless symmetric Boolean adjacency matrix on Fin n, with ordinary triangle-freeness and a witness to the lower bound on independence. There are no analytic, structural or computational assumptions in the statement. The proof does not give an explicit ε or settle unrestricted Erdős Problem #128.

## Proof map

1. `ObstructionSequence` and `FiniteSaturatedSequence` turn failure into an even, growing sequence. Razborov's greedy argument gives vanishing marked degree shortfall. The proof constructs marked cut compactness and transfers triangle density, fractional half energy and degrees.
2. `EndpointSaturation` rules out low outside profiles using the exact weighted Case 2 and a countable complementary-pair allocation. `CappedSampleBank` extracts active paired cells and bounds each side by 1/5 using independent sets in the actual finite approximants.
3. `BankClassify` proves that only a balanced C5 or Petersen kernel can remain. The outside-only greedy dual has four scalar patterns or a strict pivot. The pivot, two (2,1) blocks and the genuine two-heavy case have strict explicit measurable halves. The C5 and Petersen proofs also rule out missing allowed edges.
4. `FinalTemplateStability` transports the binary cut limit to a finite edit model and applies the verified C5 and Petersen local stability arguments of [Norin and Yepremyan](https://arxiv.org/abs/1311.5818). `FiniteKernelFloor` rounds to an ordinary floor half.

The separate paper notes are retained as provenance. Some of their references to pending formalization describe earlier stages.

## Reproduction

Pinned Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52; Mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612. Build the Mathlib Lean library (or populate its pin-matched cache) and all package dependencies. Then run:

```sh
export LEAN_BIN=/path/to/pinned/lean
export MATHLIB_LEAN_PATH=/path/to/mathlib/.lake/build/lib/lean:/path/to/package/.lake/build/lib/lean
bash graphon/replay-full-proof.sh
```

Use every package's binary-library path as needed. The script checks all 212 modules in the exact dependency closure from sources in a fresh temporary directory. The endpoint's axiom report is `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide` or new axiom is used.
