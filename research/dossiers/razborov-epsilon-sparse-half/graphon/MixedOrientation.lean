import TwoSignatureCost

namespace SparseHalfCountableEndpoint

/-- Four A-signature cells; costs count which of the two chosen outside
sides each cell sees. The four cell capacities and masses are scale-ten. -/
def FourCellFill (x b l r C : ℝ) : Prop :=
  ∃ m₀ m₁ m₂ m₃ : ℝ,
    0≤m₀ ∧ m₀≤x ∧ 0≤m₁ ∧ m₁≤2-x ∧
    0≤m₂ ∧ m₂≤2-x ∧ 0≤m₃ ∧ m₃≤x ∧
    m₀+m₁+m₂+m₃=b ∧ l*m₁+r*m₂+(l+r)*m₃≤C

theorem mixed_generic (x b l r : ℝ) (hx : 1≤x) (hx' : x≤2)
    (hb : 0≤b) (hb' : b≤3) (hl : 0≤l) (hlr : l≤r) :
    FourCellFill x b l r (r*max 0 (b-1)) := by
  have hr : 0≤r := hl.trans hlr
  have four := SparseHalfTwoSignatureCost.fourCells 4 x b r (by norm_num; exact hx)
    (by norm_num; exact hx') (by norm_num; exact hb') hr
  norm_num at four
  by_cases h0 : b≤x
  · refine ⟨b,0,0,0,hb,h0,le_rfl,by linarith,le_rfl,by linarith,le_rfl,by linarith,by ring,?_⟩
    simpa using mul_nonneg hr (le_max_left (0:ℝ) (b-1))
  by_cases h1 : b≤2
  · refine ⟨x,b-x,0,0,by linarith,le_rfl,by linarith,by linarith,
      le_rfl,by linarith,le_rfl,by linarith,by ring,?_⟩
    have u := mul_le_mul_of_nonneg_right hlr (show 0≤b-x by linarith)
    have v := mul_le_mul_of_nonneg_left (le_max_right (0:ℝ) (b-1)) hr
    nlinarith
  by_cases h2 : b≤4-x
  · refine ⟨x,2-x,b-2,0,by linarith,le_rfl,by linarith,le_rfl,
      by linarith,by linarith,le_rfl,by linarith,by ring,?_⟩
    have u := mul_le_mul_of_nonneg_right hlr (show 0≤2-x by linarith)
    have v := mul_le_mul_of_nonneg_left (le_max_right (0:ℝ) (b-1)) hr
    nlinarith
  · refine ⟨x,2-x,2-x,b-(4-x),by linarith,le_rfl,by linarith,le_rfl,
      by linarith,le_rfl,by linarith,by linarith,by ring,?_⟩
    have u := mul_le_mul_of_nonneg_right hlr (show 0≤2-x by linarith)
    have v := mul_le_mul_of_nonneg_right hlr (show 0≤b-(4-x) by linarith)
    rw [max_eq_right (by linarith : 0≤b-x),max_eq_right (by linarith : 0≤b-(4-x))] at four
    nlinarith

theorem mixed_exceptional_aligned (x : ℝ) (hx : 1≤x) (hx' : x≤2) :
    FourCellFill x 2 (3/2) (3/2) (3/2) := by
  refine ⟨x,2-x,0,0,by linarith,le_rfl,by linarith,le_rfl,
    le_rfl,by linarith,le_rfl,by linarith,by ring,?_⟩
  linarith

/-- The actual weights, not a max-weight relaxation, remove the only
potential non-strict endpoint when the favorable class is crossed. -/
theorem mixed_exceptional_crossed (x : ℝ) (hx : 1≤x) (hx' : x≤2) :
    FourCellFill x (7/3) (7/6) (3/2) (5/3) := by
  by_cases h : x≤5/3
  · refine ⟨x,2-x,1/3,0,by linarith,le_rfl,by linarith,le_rfl,
      by norm_num,by linarith,le_rfl,by linarith,by ring,?_⟩
    linarith
  · refine ⟨x,2-x,2-x,x-5/3,by linarith,le_rfl,by linarith,le_rfl,
      by linarith,le_rfl,by linarith,by linarith,by ring,?_⟩
    ring_nf
    norm_num

/-- Choosing favorable signature orientations whose selected outside mass
is large enough turns the strict two-heavy scalar estimate into a fill. -/
theorem mixed_from_endpoint (x S X l r : ℝ)
    (hx : 1≤x) (hx' : x≤2) (hX : 2≤X) (hSX : X≤S) (hS : S≤4)
    (hl : 0≤l) (hlr : l≤r) (strict : r*(4-X)<2) :
    ∃ C<2, FourCellFill x (5-S) l r C := by
  refine ⟨r*max 0 (5-S-1),?_,mixed_generic x (5-S) l r hx hx' (by linarith) (by linarith) hl hlr⟩
  rw [max_eq_right (by linarith : 0≤5-S-1)]
  exact (mul_le_mul_of_nonneg_left (show 5-S-1≤4-X by linarith) (hl.trans hlr)).trans_lt strict

#print axioms mixed_from_endpoint
#print axioms mixed_exceptional_aligned
#print axioms mixed_exceptional_crossed
end SparseHalfCountableEndpoint
