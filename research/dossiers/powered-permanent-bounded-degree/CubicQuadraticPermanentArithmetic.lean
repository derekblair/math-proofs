import Mathlib.Tactic.Linarith

namespace CubicQuadraticPermanent

theorem cubic_no_wrap (a : ℤ) (hl : -2 ≤ a) (hr : a ≤ 2)
    (h : 3 ∣ a) : a = 0 := by omega

theorem generic_no_wrap (g a : ℤ) (hg : 0 < g)
    (hl : -g < a) (hr : a < g) (h : g ∣ a) : a = 0 := by
  rcases h with ⟨b, rfl⟩
  by_cases hb : b = 0
  · simp [hb]
  · by_cases hpos : 0 < b
    · have h1 : 1 ≤ b := by omega
      have h2 := mul_le_mul_of_nonneg_left h1 hg.le
      simp only [mul_one] at h2
      omega
    · have h1 : b ≤ -1 := by omega
      have h2 := mul_le_mul_of_nonneg_left h1 hg.le
      simp only [mul_neg, mul_one] at h2
      omega

theorem additive_from_rectangles {ι : Type*} (M : ι → ι → ℤ) (a : ι)
    (diag : ∀ i, M i i = 0)
    (rect : ∀ i k j l, M i j + M k l = M i l + M k j) :
    ∀ i j, M i j = M i a - M j a := by
  intro i j
  have h := rect i j j a
  have hj := diag j
  omega

theorem extreme_lift_contradiction {ι : Type*} (M : ι → ι → ℤ)
    (a i j : ι) (t : ℤ) (ht : 0 < t)
    (hadd : M i j = M i a - M j a)
    (hl : M i a = t) (hr : M j a = -t) :
    ¬ (M i j ≤ t) := by omega

#print axioms cubic_no_wrap
#print axioms generic_no_wrap
#print axioms additive_from_rectangles
#print axioms extreme_lift_contradiction

end CubicQuadraticPermanent
