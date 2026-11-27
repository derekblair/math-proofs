import Mathlib.Tactic.Linarith

namespace CompactDagFailure

theorem full_side_strict {ι κ : Type*} (left : ι → ℕ) (right : κ → ℕ)
    (h : ∀ i j, left i < right j) (r : ℕ) :
    (∀ i, left i < r) ∨ (∀ j, r < right j) := by
  classical
  by_cases hl : ∀ i, left i < r
  · exact Or.inl hl
  · right
    push Not at hl
    obtain ⟨i, hi⟩ := hl
    intro j
    exact lt_of_le_of_lt hi (h i j)

theorem full_side_nonstrict {ι κ : Type*} (left : ι → ℕ) (right : κ → ℕ)
    (h : ∀ i j, left i < right j) (r : ℕ) :
    (∀ i, left i < r) ∨ (∀ j, r ≤ right j) := by
  rcases full_side_strict left right h r with l | rr
  · exact Or.inl l
  · exact Or.inr (fun j => (rr j).le)

theorem top_two_one_exclusion {ι C : Type*} [Preorder C] (c : ι → C)
    (first second bad : ι) (hs : second ≠ first)
    (hfirst : ∀ z, c first ≤ c z)
    (hsecond : ∀ z, z ≠ first → c second ≤ c z) :
    ∃ chosen, (chosen = first ∨ chosen = second) ∧ chosen ≠ bad ∧
      ∀ z, z ≠ bad → c chosen ≤ c z := by
  by_cases h : first = bad
  · exact ⟨second, Or.inr rfl, fun e => hs (e.trans h.symm),
      fun z hz => hsecond z (fun e => hz (e.trans h))⟩
  · exact ⟨first, Or.inl rfl, h, fun z _ => hfirst z⟩

theorem crossing_intervals (i j r : ℕ) :
    (i < r ∧ r < j) ↔ (i + 1 ≤ r ∧ r + 1 ≤ j) := by omega

theorem shifted_latest (b l x y : ℚ) (j i : ℕ)
    (hL : 2 * b < l) (hB : 0 ≤ b) (hx : x ≤ b) (hy : -b ≤ y)
    (hji : j < i) :
    x - (i : ℚ) * l < y - (j : ℚ) * l := by
  have hl : 0 ≤ l := by linarith
  have hh : (j : ℚ) + 1 ≤ (i : ℚ) := by exact_mod_cast hji
  have hmul := mul_le_mul_of_nonneg_right hh hl
  linarith

#print axioms full_side_strict
#print axioms full_side_nonstrict
#print axioms top_two_one_exclusion
#print axioms crossing_intervals
#print axioms shifted_latest

end CompactDagFailure
