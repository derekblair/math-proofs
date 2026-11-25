import Mathlib

/-! # Prime-power fiber-compatibility characterization (ES-004) -/

variable {p : ℕ} [Fact p.Prime]

def A_map (s k : ZMod p) : ZMod p → ZMod p := fun u => -(u * s^2) - k * s

def PairClosed (s k : ZMod p) (D D' : Finset (ZMod p)) : Prop :=
  ∀ u ∈ D, A_map s k u ∈ D'

theorem fiber_compat_pair_iff {s t k : ZMod p} (hts : t * s = 1) (hs : s ≠ 0)
    (D D' : Finset (ZMod p)) :
    (PairClosed s k D D' ∧ PairClosed t k D' D) ↔ D' = Finset.image (A_map s k) D := by
  sorry
