import GeometricLinkCorners

namespace RobustFolkman.GeometricGap
open MeasureTheory Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def linkTriangleCount (g : EdgeGraph V) (v : V) : ℝ :=
  ∑ T∈triangles g, rootIncidence T v

noncomputable def linkMixedCount (g : EdgeGraph V) (c : Finset V→Bool) (v : V) : ℝ :=
  ∑ T∈triangles g, rootMixed T c v

theorem sum_link_triangles (g : EdgeGraph V) :
    (∑ v : V, linkTriangleCount g v) = 3*((triangles g).card:ℝ) := by
  unfold linkTriangleCount
  rw [Finset.sum_comm]
  calc
    _ = ∑ _ ∈ triangles g, (3:ℝ) := by
      apply Finset.sum_congr rfl
      intro T h
      exact local_link_incidence T (mem_triangles.mp h).2
    _ = _ := by simp [mul_comm]

theorem mono_contribution_sum (g : EdgeGraph V) (c : Finset V→Bool) :
    (∑ T∈triangles g, monoContribution T c)=((mono (triangles g) c).card:ℝ) := by
  classical
  unfold monoContribution mono
  rw [← Finset.sum_filter]
  simp

theorem link_corners_sum (g : EdgeGraph V) (c : Finset V→Bool) :
    (∑ v : V, linkMixedCount g c v) + 2*((mono (triangles g) c).card:ℝ) =
      2*((triangles g).card:ℝ) := by
  have h : (∑ T∈triangles g, ((∑ v : V, rootMixed T c v)+2*monoContribution T c)) =
      ∑ _ ∈triangles g, (2:ℝ) := by
    apply Finset.sum_congr rfl
    intro T mt
    exact local_link_corner_count T (mem_triangles.mp mt).2 c
  rw [Finset.sum_add_distrib,←Finset.mul_sum,mono_contribution_sum,←Finset.sum_comm] at h
  simpa [linkMixedCount,mul_comm] using h

/-- A linkwise cut bound gives a universal two-color monochromatic
margin by exact triangle-corner accounting. -/
theorem monochromatic_margin_from_link_cut (g : EdgeGraph V) (ρ : ℝ)
    (cut : ∀ (v : V) (c : Finset V→Bool),
      linkMixedCount g c v ≤ ((1+ρ)/2)*linkTriangleCount g v) :
    coloringMargin ((1-3*ρ)/4) g=true := by
  unfold coloringMargin
  apply decide_eq_true
  intro c
  have total : (∑ v : V, linkMixedCount g c v) ≤
      ((1+ρ)/2)*(3*((triangles g).card:ℝ)) := by
    have h := Finset.sum_le_sum fun v (_ : v∈(univ : Finset V)) => cut v c
    rwa [←Finset.mul_sum,sum_link_triangles] at h
  have eq := link_corners_sum g c
  linarith only [total,eq]

#print axioms monochromatic_margin_from_link_cut
end RobustFolkman.GeometricGap
