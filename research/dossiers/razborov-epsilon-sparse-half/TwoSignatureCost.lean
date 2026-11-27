import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseHalfTwoSignatureCost

/-- Given two half-neighborhood signatures, the A vertices fall into four
cells of weights x,a/2-x,a/2-x,x. Charge at most p for each neighbor side.
A fill starts with the cell avoiding both, then the two single-incidence
cells, and ends with the double-incidence cell. -/
theorem fourCells (a x s p : ℝ)
    (hx : a/4 ≤ x) (hx' : x ≤ a/2)
    (hs : s ≤ 3*a/4) (hp : 0 ≤ p) :
    p*(max 0 (s-x) + max 0 (s-(a-x))) ≤ p*max 0 (s-a/4) := by
  apply mul_le_mul_of_nonneg_left _ hp
  by_cases he : s≤a-x
  · rw [max_eq_left (sub_nonpos.mpr he), add_zero]
    exact max_le_max_left _ (by linarith)
  · have h0 : 0≤s-x := by linarith
    have h1 : 0≤s-(a-x) := by linarith
    rw [max_eq_right h0,max_eq_right h1]
    have ht := le_max_right (0:ℝ) (s-a/4)
    linarith

/-- With isolated outside mass h, the two alternate orientations have
total regular capacity 2W-h. If both shorter, their deficits add to h:
some heavy side's size minus its deficit is at least 1/10. -/
theorem pivot_deficit (W h R S p q : ℝ)
    (hcap : R+S=2*W-h) (hsize : 1/5+h≤p+q) :
    1/10 ≤ p-(W-R) ∨ 1/10 ≤ q-(W-S) := by
  by_contra! hn
  linarith [hn.1,hn.2]

/-- Sufficient degree envelope when the deficient orientation is topped up
by vertices isolated in the outside graph. -/
theorem pivot_cost (a W R p : ℝ) (ha : 0≤a) (hW : W=(1-a)/2)
    (hf : 1/10≤p-(W-R)) :
    (a/4)*(R-p)+(a/2)*(W-R)≤1/50 := by
  have h1 := mul_nonneg ha (show 0≤p-(W-R)-1/10 by linarith)
  nlinarith [sq_nonneg (a-2/5)]

#print axioms fourCells
#print axioms pivot_cost
end SparseHalfTwoSignatureCost
