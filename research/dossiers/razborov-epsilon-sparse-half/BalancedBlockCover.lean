import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseHalfBalancedBlockCover

/-- Two complementary constructions suffice for balanced saturated blocks.
If the largest side is light, use only outside-vertices. If a block has
both sides heavy, use the A-half avoiding a side of this block, then choose
the better-oriented sides of the other blocks. -/
theorem cover (a p : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 2/5) :
    p*(a/2) ≤ 1/50 ∨ (a/4)*((1-a)/2-p) ≤ 1/50 := by
  by_cases hp : p ≤ (1/10:ℝ)
  · left
    have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ a/2 by linarith)
    linarith
  · right
    have hh := mul_nonneg (show 0 ≤ a by exact ha) (show 0 ≤ p-1/10 by linarith)
    nlinarith [sq_nonneg (a-2/5)]

/-- Two opposite orientation profiles allocate all outside mass, so one
has capacity at least half the outside, with heavy side size available. -/
theorem enough_oriented_capacity (a L R : ℝ)
    (h : L+R = 1-a) :
    (1-a)/2 ≤ L ∨ (1-a)/2 ≤ R := by
  by_contra! z
  linarith [z.1, z.2]

#print axioms cover
#print axioms enough_oriented_capacity
end SparseHalfBalancedBlockCover
