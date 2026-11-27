import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseHalfSaturatedOrthogonal

/-- Every two-coordinate projection of the eight A cells has unit
capacity per pattern. Their weights therefore depend only on parity. -/
theorem parity (w000 w001 w010 w011 w100 w101 w110 w111 : ℝ)
    (a0:w000+w001=1) (a1:w010+w011=1) (a2:w100+w101=1) (a3:w110+w111=1)
    (b0:w000+w010=1) (b1:w001+w011=1) (b2:w100+w110=1) (b3:w101+w111=1)
    (c0:w000+w100=1) (c1:w001+w101=1) (c2:w010+w110=1) (c3:w011+w111=1) :
    w011=w000 ∧ w101=w000 ∧ w110=w000 ∧
    w001=1-w000 ∧ w010=1-w000 ∧ w100=1-w000 ∧ w111=1-w000 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

/-- Normalize by ten. Taking one side of each of the three unit blocks
leaves mass two to pick from A. Orient at a least-mass zero cell then
fill all remaining from the three cells of edge-cost one. -/
theorem sparse_singles (x : ℝ) (hx0 : 0≤x) (hx : x≤1/2) :
    ∃ y : ℝ, 0≤y ∧ y≤1-x ∧ x+3*y=2 ∧
      3*y≤2 ∧ (0<x → 3*y<2) := by
  refine ⟨(2-x)/3, ?_, ?_, ?_, ?_, ?_⟩ <;> try linarith
  intro hp
  linarith

/-- A non-orthogonal pair reduces the cost of the opposite-side pivot
strictly below the target for three unit complementary blocks. -/
theorem nonorthogonal (x y : ℝ) (hx : x≠1) :
    min x (2-x) + min y (2-y)<2 := by
  have hy : min y (2-y)≤1 := by
    by_cases hk : y≤1
    · exact (min_le_left _ _).trans hk
    · exact (min_le_right _ _).trans (by linarith)
  have hxm : min x (2-x)<1 := by
    rcases lt_or_gt_of_ne hx with hk | hk
    · exact (min_le_left _ _).trans_lt hk
    · exact (min_le_right _ _).trans_lt (by linarith)
  linarith

#print axioms parity
#print axioms sparse_singles
#print axioms nonorthogonal
end SparseHalfSaturatedOrthogonal
