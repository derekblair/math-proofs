import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace BooleanSignedPhaseRank

theorem unit_phase_atom (a b c d : ℝ) (h₁ : a^2 + b^2 = 1)
    (h₂ : c^2 + d^2 = 1) :
    ((a-c)^2 + (b-d)^2) / 2 = 1 - (a*c + b*d) := by
  nlinarith

theorem reflection_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ℝ) (hx : (Fintype.card ι : ℝ) * x^2 = 2*x) (i j : ι) :
    (∑ k : ι, (x - (if i = k then (1:ℝ) else 0)) *
      (x - (if k = j then (1:ℝ) else 0))) = (if i = j then 1 else 0) := by
  classical
  let e : ι → ι → ℝ := fun a b => if a = b then 1 else 0
  change (∑ k, (x - e i k) * (x - e k j)) = e i j
  have he₁ : ∑ k, e i k * x = x := by simp [e]
  have he₂ : ∑ k, x * e k j = x := by simp [e]
  have he₃ : ∑ k, e i k * e k j = e i j := by
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro k hk hki
      simp [e, Ne.symm hki]
    · simp
  calc
    (∑ k, (x - e i k) * (x - e k j)) =
        ∑ k, (x^2 - e i k*x - x*e k j + e i k*e k j) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = e i j := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, he₁, he₂, he₃,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      linarith

theorem squared_pairing_gain_on_eight :
    (((2 : ℚ) * 7)^2 / (8 * 7)) / 3 = 7 / 6 := by
  norm_num

end BooleanSignedPhaseRank

#print axioms BooleanSignedPhaseRank.unit_phase_atom
#print axioms BooleanSignedPhaseRank.reflection_square
#print axioms BooleanSignedPhaseRank.squared_pairing_gain_on_eight
