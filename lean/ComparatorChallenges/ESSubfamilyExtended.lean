import Mathlib

/-! # Generalized Erdős–Straus sub-family identity (SS-004) -/

namespace ESSubfamilyExtended

theorem generalized_subfamily_identity
    (q A r e f u m k V₀ s : ℤ)
    (S Mp : ℤ)
    (hq : 0 < q) (hA : 0 < A) (hr : 0 < r) (he : 0 < e)
    (hfpos : 0 < f) (hm3 : 3 ≤ m) (hmod4 : m ≡ 3 [ZMOD 4])
    (hS : S = 510510 * q) (hM : Mp = 4 * S)
    (hAS : A ∣ S)
    (hur : u * r = A * S)
    (hf : f * S = r * q * e)
    (hk : m * k = 1 + 4 * u)
    (hV₀ : q * e * k * V₀ ≡ u [ZMOD A])
    (hs : s ≡ -m + 4 * q * e * V₀ [ZMOD 4 * q * e * (A / ((Int.gcd A (q*e*k) : ℕ) : ℤ))])
    (h1s : 1 ≤ s) :
    ∀ t : ℤ, 0 ≤ t →
      (4 : ℚ) / ((Mp * t + s : ℤ) : ℚ) =
        1 / ((S * t + q * e * ((s + m) / (4 * q * e)) : ℤ) : ℚ) +
        1 / (((Mp * t + s : ℤ) : ℚ) * A *
          (((S / A) * k * t + (s * k + 1) / (4 * A) : ℤ) : ℚ)) +
        1 / (((r * t + f * ((s + m) / (4 * q * e)) : ℤ) : ℚ) *
          (((S / A) * k * t + (s * k + 1) / (4 * A) : ℤ) : ℚ)) := by
  sorry

end ESSubfamilyExtended
