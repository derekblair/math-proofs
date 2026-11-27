import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PermanentSquareExponential

theorem coupled_moment_bound (x₁ x₃ : ℚ)
    (h₂ : 1 + 2 * x₁ ≤ 2) (h₆ : 1 + 6 * x₁ + 20 * x₃ ≤ 8) :
    x₁ + x₃ ≤ 7 / 10 := by linarith

theorem odd_binomial_step (j : ℚ) (hj : 5 ≤ j) :
    10 * (j + 1) * (j + 2) ≤ 3 * (2 * j + 1) * (2 * j + 3) := by
  nlinarith [sq_nonneg (j - 5)]

theorem tail_telescope (u : ℕ → ℚ) (h : ∀ j, u (j + 1) ≤ (3 / 10) * u j) :
    ∀ j, (7 / 10) * (∑ i ∈ Finset.range j, u i) + u j ≤ u 0 := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    linarith [h j]

theorem odd_mass_below_one (x₁ x₃ s : ℚ)
    (h₂ : 1 + 2 * x₁ ≤ 2) (h₆ : 1 + 6 * x₁ + 20 * x₃ ≤ 8)
    (hTail : (7 / 10) * s ≤ 8 / 63) : x₁ + x₃ + s < 1 := by
  have h := coupled_moment_bound x₁ x₃ h₂ h₆
  linarith

#print axioms coupled_moment_bound
#print axioms odd_binomial_step
#print axioms tail_telescope
#print axioms odd_mass_below_one

end PermanentSquareExponential
