import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace PermanentUniformApproximation

theorem pairwise_rect_seed {ι : Type*} [Fintype ι] (u : ι → ℚ)
    (hu : (∑ i, u i) = 0) :
    (∑ i, ∑ j, (u i - u j)^2) =
      2 * (Fintype.card ι : ℚ) * (∑ i, (u i)^2) := by
  classical
  calc
    (∑ i, ∑ j, (u i - u j)^2) =
        ∑ i, ∑ j, ((u i)^2 + (u j)^2 - (2 * u i) * u j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = ∑ i, ((Fintype.card ι : ℚ) * (u i)^2 + (∑ j, (u j)^2)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hu]
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
        ring


theorem rectangle_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : ι → κ → ℚ) (hr : ∀ i, (∑ a, H i a) = 0)
    (hc : ∀ a, (∑ i, H i a) = 0) :
    (∑ i, ∑ j, ∑ a, ∑ b, ((H i a - H j a) - (H i b - H j b))^2) =
      4 * (Fintype.card ι : ℚ) * (Fintype.card κ : ℚ) * (∑ i, ∑ a, (H i a)^2) := by
  classical
  calc
    _ = ∑ i, ∑ j, (2 * (Fintype.card κ : ℚ)) * ∑ a, (H i a - H j a)^2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact pairwise_rect_seed (fun a => H i a - H j a) (by simp [Finset.sum_sub_distrib, hr])
    _ = (2 * (Fintype.card κ : ℚ)) * ∑ a, ∑ i, ∑ j, (H i a - H j a)^2 := by
      simp only [← Finset.mul_sum]
      apply congrArg (fun t : ℚ => (2 * (Fintype.card κ : ℚ)) * t)
      calc
        (∑ i, ∑ j, ∑ a, (H i a - H j a)^2) =
            ∑ i, ∑ a, ∑ j, (H i a - H j a)^2 := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = (2 * (Fintype.card κ : ℚ)) *
        ∑ a, (2 * (Fintype.card ι : ℚ)) * ∑ i, (H i a)^2 := by
      apply congrArg (fun t : ℚ => (2 * (Fintype.card κ : ℚ)) * t)
      apply Finset.sum_congr rfl
      intro a _
      exact pairwise_rect_seed (fun i => H i a) (hc a)
    _ = _ := by
      simp only [← Finset.mul_sum]
      have hs : (∑ a, ∑ i, (H i a)^2) = ∑ i, ∑ a, (H i a)^2 := Finset.sum_comm
      rw [hs]
      ring

theorem tangent_zero_obstruction (c a b : ℚ)
    (hc : 0 < c) (ha : 0 < a) (h : c * a ≤ b) : b ≠ 0 := by
  exact ne_of_gt (lt_of_lt_of_le (mul_pos hc ha) h)

#print axioms pairwise_rect_seed
#print axioms rectangle_identity
#print axioms tangent_zero_obstruction

end PermanentUniformApproximation
