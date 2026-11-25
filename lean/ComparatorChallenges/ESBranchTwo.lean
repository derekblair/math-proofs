import Mathlib

/-! # Branch-2 degeneracy and divisor-closed family theorem (ES-004) -/

namespace ESBranchTwo

theorem branch2_collapse (A r₁ XSTEP x₀ p q m t : ℤ)
    (h1 : (r₁ + A) * XSTEP = m * A * r₁ * p)
    (h2 : (r₁ + A) * x₀ = m * A * r₁ * q) :
    (r₁ + A) * (XSTEP * t + x₀) = m * A * r₁ * (p * t + q) := by
  sorry

theorem family_identity (t k : ℕ) :
    (4 : ℚ) / ((2042040 : ℚ) * t + (264 * (k : ℚ) + 73))
      = 1 / ((510510 : ℚ) * t + (264 * (k : ℚ) + 73 + 15) / 4)
      + 1 / (((2042040 : ℚ) * t + (264 * (k : ℚ) + 73))
          * ((1531530 : ℚ) * t + (3 * (264 * (k : ℚ) + 73) + 1) / 4))
      + 1 / (((46410 : ℚ) * t + (264 * (k : ℚ) + 73 + 15) / 44)
          * ((1531530 : ℚ) * t + (3 * (264 * (k : ℚ) + 73) + 1) / 4)) := by
  sorry

theorem branch2_m_mod8_refuted :
    ((97 : ℕ) % 8 = 1 ∧ 4 ∣ 97 + 3 ∧ 25 * 4 = 97 + 3 ∧ 15 ∣ 3 * 25 ∧
      3 * 3 ≤ 2 * 15 ∧ 3 ≤ 3 ∧ (3 : ℕ) % 4 = 3 ∧ (97 : ℕ) % 24 = 1)
    ∧ (3 : ℕ) % 8 ≠ 7 := by
  sorry

end ESBranchTwo
