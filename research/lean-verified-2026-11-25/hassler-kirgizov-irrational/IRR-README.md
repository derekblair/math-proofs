# Irrational limiting popularity of a consecutive permutation pattern

An affirmative answer to question 3 in §5 of [Hassler and Kirgizov, Emerging consecutive pattern avoidance](https://dmtcs.episciences.org/en/articles/16861). Keep the five length-four patterns 1234, 2134, 1324, 1243, 2143 and forbid the other 19. Pattern 2143 has limiting popularity (1 - (2/5)\sqrt{5}\), approximately 0.10557. No earlier answer was found in the public novelty check; this is not a claim of absolute priority.

## Check
Use Lean 4.34.1 with the matching official Mathlib tag v4.34.1, commit d13f23b723b8a846827a245b89c10fc7d3f11612.
```bash
git clone --branch v4.34.1 --depth 1 https://github.com/leanprover-community/mathlib4.git
(cd mathlib4 && lake exe cache get Mathlib/Tactic.lean \
  Mathlib/Data/Fintype/EquivFin.lean Mathlib/Data/Finset/Card.lean Mathlib/Data/Finset/Sort.lean \
  Mathlib/Topology/Instances/Real/Lemmas.lean Mathlib/Analysis/SpecificLimits/Basic.lean \
  Mathlib/Analysis/SpecificLimits/Normed.lean Mathlib/NumberTheory/Real/GoldenRatio.lean \
  Mathlib/Algebra/Field/GeomSum.lean)
bash verify-irr.sh mathlib4
```

Main theorem: `FibPopularity.question3` (actual permutation avoidance, eventually nonempty classes, surviving pattern, real limit, irrationality). Printed axioms: `propext`, `Classical.choice`, `Quot.sound`. The five support files from the Conjecture 5.1 project are included to provide the shared source definitions; that refutation is not an assumption of this proof. The Python enumeration validates small cases independently and is not imported into Lean.
