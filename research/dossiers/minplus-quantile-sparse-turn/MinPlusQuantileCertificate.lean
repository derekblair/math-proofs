import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Find

namespace MinPlusQuantile

def PositiveSuffix (diff : ℕ → ℤ) (l r : ℕ) : Prop :=
  ∃ q, l ≤ q ∧ q < r ∧ 0 < diff q ∧ ∀ k, l ≤ k → k < q → diff k = 0

theorem positive_suffix_monotone (diff : ℕ → ℤ) (r i j : ℕ)
    (mountain : ∀ a b, i ≤ a → a < b → b < r → ¬ (diff a < 0 ∧ 0 < diff b))
    (hij : i ≤ j) (h : PositiveSuffix diff j r) :
    PositiveSuffix diff i r := by
  classical
  rcases h with ⟨q, hqj, hqr, hqpos, _⟩
  have hq : i ≤ q ∧ q < r ∧ diff q ≠ 0 :=
    ⟨hij.trans hqj, hqr, ne_of_gt hqpos⟩
  let hx : ∃ k, i ≤ k ∧ k < r ∧ diff k ≠ 0 := ⟨q, hq⟩
  let k := Nat.find hx
  have hk : i ≤ k ∧ k < r ∧ diff k ≠ 0 := Nat.find_spec hx
  have hkq : k ≤ q := Nat.find_min' hx hq
  have hkpos : 0 < diff k := by
    rcases lt_or_eq_of_le hkq with hh | he
    · have hn : ¬ diff k < 0 := fun hn => mountain k q hk.1 hh hqr ⟨hn, hqpos⟩
      omega
    · simpa [he] using hqpos
  refine ⟨k, hk.1, hk.2.1, hkpos, ?_⟩
  intro u hu hu'
  by_contra hn
  have htest : i ≤ u ∧ u < r ∧ diff u ≠ 0 := ⟨hu, lt_trans hu' hk.2.1, hn⟩
  exact Nat.find_min hx hu' htest

theorem weighted_pivot_shrinks (total group removed : ℕ)
    (hhalf : total ≤ 2 * group) (hremove : group ≤ 2 * removed)
    (hR : removed ≤ total) :
    4 * (total - removed) ≤ 3 * total := by omega

#print axioms positive_suffix_monotone
#print axioms weighted_pivot_shrinks

end MinPlusQuantile
