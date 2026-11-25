import Mathlib

/-! # Quadratic-residue core cardinality modulo `24 * ∏ p` (ES-003) -/

namespace ESQRCoreCount

def residueModulus (s : Finset ℕ) : ℕ := 24 * ∏ p ∈ s, p

def targetResidues (s : Finset ℕ) : Set (ZMod (residueModulus s)) :=
  {a | IsUnit a ∧ ZMod.castHom (show 24 ∣ residueModulus s from dvd_mul_right _ _) (ZMod 24) a = 1}

def qrResidues (s : Finset ℕ) : Set (ZMod (residueModulus s)) :=
  {a | a ∈ targetResidues s ∧ IsSquare a}

theorem qr_residue_count (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h5 : ∀ p ∈ s, 5 ≤ p) :
    Nat.card (qrResidues s) = Nat.card (targetResidues s) / 2 ^ s.card := by
  sorry

end ESQRCoreCount
