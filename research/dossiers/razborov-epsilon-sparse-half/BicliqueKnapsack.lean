import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace SparseHalfBicliqueKnapsack

/-- Exact restricted cost within one complete bipartite block at fixed total
mass. Picking from its larger side first attains this lower bound. -/
theorem block_lower (p q x y : ℝ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ p) (hy : y ≤ q) (hqp : q ≤ p) :
    p * max 0 (x+y-p) ≤ x*y := by
  by_cases h0 : x+y-p ≤ 0
  · simpa [max_eq_left h0] using mul_nonneg hx0 hy0
  · rw [max_eq_right (by linarith : 0 ≤ x+y-p)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr (hy.trans hqp))]

/-- An explicit profile attaining the block lower envelope for any admissible
total mass. -/
theorem block_attain (p q s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hqp : q ≤ p)
    (hs : 0 ≤ s) (hcap : s ≤ p+q) :
    ∃ x y : ℝ, 0 ≤ x ∧ x ≤ p ∧ 0 ≤ y ∧ y ≤ q ∧ x+y=s ∧
      x*y=p*max 0 (s-p) := by
  by_cases h : s ≤ p
  · refine ⟨s, 0, hs, h, le_rfl, hq, by ring, ?_⟩
    simp [max_eq_left (sub_nonpos.mpr h)]
  · refine ⟨p, s-p, hp, le_rfl, by linarith, by linarith, by ring, ?_⟩
    rw [max_eq_right (by linarith : 0 ≤ s-p)]

#print axioms block_lower
#print axioms block_attain
end SparseHalfBicliqueKnapsack
