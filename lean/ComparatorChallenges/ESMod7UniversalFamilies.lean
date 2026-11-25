import Mathlib

/-! # Mod-7 universal Erdős–Straus covering families (ES-003) -/

namespace ESCovering

def Covered (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / n = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

def CoversClass (M s : ℕ) : Prop := ∀ t : ℕ, Covered (M * t + s)

end ESCovering

namespace ESMod7UniversalFamilies

theorem fam1_covers (k₀ : ℕ) (hs : (24*k₀+1) % 7 = 3) :
    ESCovering.CoversClass 9240 (24*k₀+1) := by
  sorry

theorem fam2_covers (k₀ : ℕ) (hs : (24*k₀+1) % 7 = 5) :
    ESCovering.CoversClass 9240 (24*k₀+1) := by
  sorry

theorem fam3_covers (k₀ : ℕ) (hs : (24*k₀+1) % 7 = 6) :
    ESCovering.CoversClass 9240 (24*k₀+1) := by
  sorry

end ESMod7UniversalFamilies
