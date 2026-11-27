import GeometricLinkCuts

namespace RobustFolkman.GeometricGap
open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def cutCount (F : EdgeGraph V) (b : V → Bool) : ℝ := by
  classical
  exact ∑ e∈F, if Monochrom b e then 0 else 1

theorem extend_cut_count (H F : EdgeGraph V) (sub : H ⊆ F) (b : V → Bool) :
    cutCount F b ≤ cutCount H b + ((F.card:ℝ)-(H.card:ℝ)) := by
  classical
  unfold cutCount
  rw [←Finset.sum_sdiff sub]
  have h : (∑ e ∈ F \ H, (if Monochrom b e then 0 else 1 : ℝ)) ≤ ((F\H).card:ℝ) := by
    calc
      _ ≤ ∑ _e ∈ F \ H, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro e _
        split <;> norm_num
      _ = _ := by simp
  rw [Finset.card_sdiff_of_subset sub, Nat.cast_sub (Finset.card_le_card sub)] at h
  linarith only [h]

/-- Removing at most one seventh of the edges allows transfer from
a 9/16-cut bound on a subgraph to the 5/8 bound on the original graph. -/
theorem cut_transfer_one_seventh (H F : EdgeGraph V) (sub : H ⊆ F)
    (keep : (6/7:ℝ)*(F.card:ℝ) ≤ (H.card:ℝ))
    (cut : ∀ b : V → Bool, cutCount H b ≤ (9/16)*(H.card:ℝ)) :
    ∀ b : V → Bool, cutCount F b ≤ (5/8)*(F.card:ℝ) := by
  intro b
  linarith only [extend_cut_count H F sub b,keep,cut b]

#print axioms cut_transfer_one_seventh
end RobustFolkman.GeometricGap
