import Mathlib

/-! # Erdős–Straus covering identity for `n ≡ 217 (mod 264)` (ES-001) -/

theorem es_identity_217mod264 (n : ℕ) (h : n % 264 = 217) :
    (4 : ℚ) / (n : ℚ)
      = 1 / (((n : ℚ) + 3) / 4)
        + 1 / ((n : ℚ) * ((n : ℚ) + 3))
        + 1 / (((n : ℚ) * ((n : ℚ) + 3)) / 11) := by
  sorry

theorem es_covering_217mod264 (n : ℕ) (h : n % 264 = 217) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      4 * x = n + 3 ∧ y = n * (n + 3) ∧ 11 * z = n * (n + 3) ∧
      (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  sorry
