import LargeIsolateCycle

namespace SparseHalfCountableEndpoint

/-- The chosen half of A has mass two (scale ten). For either of its
outside orientations, R is total regular capacity, p of it free, and
h is the available isolate mass. The expensive isolate coefficient is
2; other regular mass has coefficient 1. -/
def PivotFill (R p h C : ℝ) : Prop :=
  ∃ regular extra : ℝ, 0≤regular ∧ regular≤R-p ∧
    0≤extra ∧ extra≤h ∧ p+regular+extra=3 ∧ regular+2*extra≤C

theorem pivot_orientation (R p h : ℝ)
    (hp : p≤2) (hpr : p≤R) (hh : 0≤h)
    (hfill : 3-R≤h) :
    PivotFill R p h (3-p+max 0 (3-R)) := by
  by_cases g : 3≤R
  · refine ⟨3-p,0,by linarith,by linarith,le_rfl,hh,by ring,?_⟩
    rw [max_eq_left (by linarith : 3-R≤0)]
    linarith
  · refine ⟨R-p,3-R,sub_nonneg.mpr hpr,le_rfl,by linarith,hfill,by ring,?_⟩
    rw [max_eq_right (by linarith : 0≤3-R)]
    linarith

/-- Strict dominant-pivot arithmetic. If one orientation supplies all
regular weight, select it. Otherwise the deficits add to the isolate
mass, and the excess free capacity ensures one fill is strictly cheap. -/
theorem strict_dominant_pivot (R S p q h : ℝ)
    (hh : 0≤h) (hp : 1<p) (hq : 1<q) (hp2 : p≤2) (hq2 : q≤2)
    (pR : p≤R) (qS : q≤S)
    (mass : R+S=6-h) (excess : 2+h<p+q) :
    (∃ C<2, PivotFill R p h C) ∨ (∃ C<2, PivotFill S q h C) := by
  by_cases rf : 3≤R
  · left
    refine ⟨3-p+max 0 (3-R),?_,pivot_orientation R p h hp2 pR hh (by linarith)⟩
    rw [max_eq_left (show 3-R≤0 by linarith)]
    linarith
  · by_cases sf : 3≤S
    · right
      refine ⟨3-q+max 0 (3-S),?_,pivot_orientation S q h hq2 qS hh (by linarith)⟩
      rw [max_eq_left (show 3-S≤0 by linarith)]
      linarith
    · have orr : 1<p-(3-R) ∨ 1<q-(3-S) := by
        by_contra! n
        linarith [n.1,n.2]
      rcases orr with gain | gain
      · left
        refine ⟨3-p+max 0 (3-R),?_,pivot_orientation R p h hp2 pR hh (by linarith)⟩
        rw [max_eq_right (show 0≤3-R by linarith)]
        linarith
      · right
        refine ⟨3-q+max 0 (3-S),?_,pivot_orientation S q h hq2 qS hh (by linarith)⟩
        rw [max_eq_right (show 0≤3-S by linarith)]
        linarith

#print axioms strict_dominant_pivot
end SparseHalfCountableEndpoint
