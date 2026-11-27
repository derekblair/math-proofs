import GeometricLinkMargin

namespace RobustFolkman.GeometricGap
open MeasureTheory Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def badLinkWeight (g : EdgeGraph V) (B : Finset V) : ℝ :=
  ∑ v ∈ B, linkTriangleCount g v

theorem local_trivial_link_cut (g : EdgeGraph V) (c : Finset V → Bool) (v : V) :
    linkMixedCount g c v ≤ linkTriangleCount g v := by
  classical
  unfold linkMixedCount linkTriangleCount
  apply Finset.sum_le_sum
  intro T _
  by_cases hv : v ∈ triVertices T
  · by_cases hc : Monochrom c (incidentSides T v) <;>
      simp [rootMixed, rootIncidence, hv, hc]
  · simp [rootMixed, rootIncidence, hv]

/-- No spectral or cut bound is used at the exceptional roots.
Their cost is their weight, not their number. -/
theorem monochromatic_weighted_link_bound (g : EdgeGraph V) (B : Finset V) (ρ : ℝ)
    (cut : ∀ v ∉ B, ∀ c : Finset V → Bool,
      linkMixedCount g c v ≤ ((1+ρ)/2)*linkTriangleCount g v) (c : Finset V → Bool) :
    ((1-3*ρ)/4)*((triangles g).card:ℝ) - ((1-ρ)/4)*badLinkWeight g B
      ≤ ((mono (triangles g) c).card:ℝ) := by
  classical
  let δ := fun v : V => if v ∈ B then linkTriangleCount g v else 0
  have per (v : V) :
      linkMixedCount g c v ≤ ((1+ρ)/2)*linkTriangleCount g v + ((1-ρ)/2)*δ v := by
    by_cases hv : v ∈ B
    · simp only [δ, if_pos hv]
      nlinarith only [local_trivial_link_cut g c v]
    · simpa only [δ, if_neg hv, mul_zero, add_zero] using cut v hv c
  have total := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => per v)
  have corr : (∑ v, δ v)=badLinkWeight g B := by
    simp only [δ, badLinkWeight, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const_zero]
  rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum, sum_link_triangles, corr] at total
  have eq := link_corners_sum g c
  linarith only [total,eq]

theorem coloring_margin_from_light_bad_links (g : EdgeGraph V) (B : Finset V)
    (light : badLinkWeight g B ≤ ((triangles g).card:ℝ)/6)
    (cut : ∀ v ∉ B, ∀ c : Finset V → Bool,
      linkMixedCount g c v ≤ ((1+(1:ℝ)/4)/2)*linkTriangleCount g v) :
    coloringMargin (1/32) g = true := by
  unfold coloringMargin
  apply decide_eq_true
  intro c
  have bound := monochromatic_weighted_link_bound g B (1/4) cut c
  linarith only [bound,light]

#print axioms monochromatic_weighted_link_bound
#print axioms coloring_margin_from_light_bad_links
end RobustFolkman.GeometricGap
