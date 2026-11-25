# Emerging consecutive pattern avoidance: Conjecture 5.1

This package refutes Conjecture 5.1 in Nathanael Hassler and Sergey Kirgizov, [Emerging consecutive pattern avoidance](https://arxiv.org/pdf/2511.02442), §5. The popularity definition is their equation (1). Only seven of the 120 length-five patterns are initially allowed. Forbidding 24531, which has limiting frequency zero, changes the limiting frequency of 21435 from zero to 1/6.

## Reproduce
Use Lean 4.34.1 and the matching official Mathlib release (tag v4.34.1, commit d13f23b723b8a846827a245b89c10fc7d3f11612). For a new checkout:
```bash
git clone --branch v4.34.1 --depth 1 https://github.com/leanprover-community/mathlib4.git
(cd mathlib4 && lake exe cache get Mathlib/Tactic.lean Mathlib/Data/Fintype/EquivFin.lean Mathlib/Data/Finset/Card.lean Mathlib/Data/Finset/Sort.lean Mathlib/Analysis/SpecificLimits/Basic.lean Mathlib/Topology/Instances/Real/Lemmas.lean)
bash verify.sh mathlib4
```
The script compiles from scratch in a temporary directory, checks that two deliberately false variants are rejected and separately brute-forces n=5 through 9. No part of the Lean statement uses that bounded brute-force control.

## Lean entry points
- `Emerging.Published`: actual pairwise order embeddings of consecutive windows on permutations of `Fin n`, actual counts, the source's denominator n|class|, and real limits. Classes are required to be eventually nonempty (both here are), and the queried initial limit is required to exist; these caveats make the refutation stronger, not weaker.
- `Emerging.A_p_zero`, `Emerging.A_q_zero`, `Emerging.B_q_sixth`: the exact three limits.
- `Emerging.refutesPublished`: negation of the published implication. Printed dependencies: `propext`, `Classical.choice`, `Quot.sound`.

## Prior-work check (2026-11-25)
The authors' arXiv v3 (9 November 2026) presents the claim as a conjecture. Exact-title and conjecture-number searches, focused queries for the allowable pattern set, and mathematical and GitHub index searches located no earlier resolution of this exact statement. Searches are not proof of absolute priority. No contact or public submission was made.
