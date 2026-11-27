import GeometricWeightedMoment

namespace RobustFolkman.GeometricGap
open Finset
variable {Ω V : Type*} [Fintype Ω] [DecidableEq V] [Fintype V]

theorem linkTriangleCount_nonneg (g : EdgeGraph V) (v : V) :
    0 ≤ linkTriangleCount g v := by
  unfold linkTriangleCount
  apply Finset.sum_nonneg
  intro T _
  unfold rootIncidence
  split <;> norm_num

theorem badLinkWeight_nonneg (g : EdgeGraph V) (B : Finset V) :
    0 ≤ badLinkWeight g B := Finset.sum_nonneg fun v _ => linkTriangleCount_nonneg g v

theorem bad_coloring_weighted_pointwise (g : EdgeGraph V) (B : Finset V) {μ : ℝ} (hμ : 0<μ)
    (cut : ∀ v ∉ B, ∀ c : Finset V → Bool,
        linkMixedCount g c v ≤ ((1+(1:ℝ)/4)/2)*linkTriangleCount g v) :
    (Moment.bad (coloringMargin (1/32)) g : ℝ) ≤
      (4/μ^2)*(((triangles g).card:ℝ)-μ)^2+(12/μ)*badLinkWeight g B := by
  let T : ℝ := (triangles g).card
  let W := badLinkWeight g B
  have Hw : 0 ≤ W := badLinkWeight_nonneg g B
  change _ ≤ (4/μ^2)*(T-μ)^2+(12/μ)*W
  by_cases ht : μ/2 ≤ T
  · by_cases hw : W ≤ μ/12
    · have light : W ≤ T/6 := by linarith
      simp only [Moment.bad, coloring_margin_from_light_bad_links g B light cut, if_true]
      positivity
    · have hb : 1 ≤ (12/μ)*W := by
        field_simp [ne_of_gt hμ]
        linarith
      have hn : 0 ≤ (4/μ^2)*(T-μ)^2 := by positivity
      refine le_trans (show (Moment.bad (coloringMargin (1/32)) g : ℝ) ≤ 1 from ?_) ?_
      · simp only [Moment.bad]; split <;> norm_num
      · linarith
  · have hb : 1 ≤ (4/μ^2)*(T-μ)^2 := by
      have h₁ : 0 ≤ μ/2-T := by linarith
      have h₂ : 0 ≤ (μ-T)+μ/2 := by linarith
      have h := mul_nonneg h₁ h₂
      field_simp [ne_of_gt hμ]
      nlinarith only [h]
    have hn : 0 ≤ (12/μ)*W := by positivity
    refine le_trans (show (Moment.bad (coloringMargin (1/32)) g : ℝ) ≤ 1 from ?_) ?_
    · simp only [Moment.bad]; split <;> norm_num
    · linarith

theorem mean_bad_coloring_weighted (p : Ω → ℝ) (g : Ω → EdgeGraph V) (B : Ω → Finset V)
    (p0 : ∀ ω, 0 ≤ p ω) {μ : ℝ} (hμ : 0<μ)
    (cut : ∀ ω, ∀ v ∉ B ω, ∀ c : Finset V → Bool,
        linkMixedCount (g ω) c v ≤ ((1+(1:ℝ)/4)/2)*linkTriangleCount (g ω) v) :
    Moment.mean p (fun ω => Moment.bad (coloringMargin (1/32)) (g ω)) ≤
      (4/μ^2)*Moment.mean p (fun ω => (((triangles (g ω)).card:ℝ)-μ)^2) +
        (12/μ)*Moment.mean p (fun ω => badLinkWeight (g ω) (B ω)) := by
  unfold Moment.mean
  rw [Finset.mul_sum, Finset.mul_sum, ←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  calc
    _ ≤ p ω * ((4/μ^2)*(((triangles (g ω)).card:ℝ)-μ)^2+(12/μ)*badLinkWeight (g ω) (B ω)) :=
      mul_le_mul_of_nonneg_left (bad_coloring_weighted_pointwise (g ω) (B ω) hμ (cut ω)) (p0 ω)
    _ = _ := by ring

#print axioms mean_bad_coloring_weighted
end RobustFolkman.GeometricGap
