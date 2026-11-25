import Mathlib

/-! # Absorbed-regime self-bound `c ≤ 320` (SS-002) -/

namespace AbsorbedBound

theorem t4_self_bound (c h a b m R g h₁ : ℤ)
    (hc : 1 ≤ c) (hh : 1 ≤ h) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : m = 4 * c - 1)
    (hab : a + b = m * h) (hle : a ≤ b)
    (hg : 1 ≤ g)
    (hR : a * b = R * g) (hh1 : h = g * h₁) (hh1pos : 1 ≤ h₁)
    (hRpos : 1 ≤ R) (hRdiv : R ∣ 30030) (h13R : ¬ (13:ℤ) ∣ R) (h13h : 13 ∣ h) :
    c ≤ 320 := by
  sorry

end AbsorbedBound
