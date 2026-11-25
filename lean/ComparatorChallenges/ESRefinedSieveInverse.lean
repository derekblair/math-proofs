import Mathlib

/-! # Refined-sieve 44-CRT selectivity and six-class inverse closure modulo 3960 (ES-006) -/

namespace ESRefinedSieve

theorem crt44_iff (s : ℤ) (h24 : s ≡ 1 [ZMOD 24]) :
    (s ≡ 7 [ZMOD 11]) ↔ (s ≡ 29 [ZMOD 44]) := by
  sorry

def sixClasses : Finset (ZMod 3960) := {2521, 721, 1201, 3361, 3841, 2041}

theorem sixClasses_exact : ∀ x : ZMod 3960,
    (x.val % 8 = 1 ∧ x.val % 5 = 1 ∧
      (x.val % 9 = 1 ∨ x.val % 9 = 4 ∨ x.val % 9 = 7) ∧
      (x.val % 11 = 2 ∨ x.val % 11 = 6)) ↔ x ∈ sixClasses := by
  sorry

theorem sixClasses_inv_closed : ∀ x : ZMod 3960, x ∈ sixClasses →
    ∃ y ∈ sixClasses, x * y = 1 := by
  sorry

end ESRefinedSieve
