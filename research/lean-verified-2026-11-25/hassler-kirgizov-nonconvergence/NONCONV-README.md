# A consecutive pattern whose popularity does not converge

A negative answer to question 4 in §5 of [Hassler and Kirgizov, Emerging consecutive pattern avoidance](https://dmtcs.episciences.org/en/articles/16861). We construct a finite avoided set of length-nine patterns with a nonempty class at every sufficiently large length, and a surviving nine-letter pattern `231564897` whose relative popularity has subsequence limits (1/44), (1/42), and (5/216) for the three length residues modulo 3.

## Reproduce
Use Lean 4.34.1 and Mathlib tag v4.34.1 (commit d13f23b723b8a846827a245b89c10fc7d3f11612).
```bash
git clone --branch v4.34.1 --depth 1 https://github.com/leanprover-community/mathlib4.git
(cd mathlib4 && lake exe cache get Mathlib/Tactic.lean \
  Mathlib/Data/Fintype/EquivFin.lean Mathlib/Data/Finset/Card.lean Mathlib/Data/Finset/Sort.lean \
  Mathlib/Topology/Instances/Real/Lemmas.lean Mathlib/Analysis/SpecificLimits/Basic.lean)
bash verify-nonconv.sh mathlib4
```
Main entry point: `Nonconv.question4`. The proof builds the 44-word overlap graph, proves all valid paths correspond bijectively to actual permutations and counts them by finite state recurrences. It counts every occurrence as a marked path, not just the number of containing permutations. `Statement.lean` supplies the literal consecutive avoidance definition and the denominator from equation (1) of the paper. The prior refutation in that file is not an assumption of this proof. The included Python script gives another exact check through n=19; Lean does not rely on it.

## Prior-work check
On November 25, 2026 the journal/arXiv publication still posed this question. An exact-title, nonconvergence, pattern and GitHub search did not find a prior resolution. This is not a claim of absolute priority.
