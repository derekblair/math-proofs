import Mathlib.Tactic
namespace PosetFlux
def mark (a i : ℕ) : ℤ := if a ≤ i then 1 else 0
def hits (a b i : ℕ) : ℤ := if a ≤ i ∧ i < b then 1 else 0
theorem recover_range {a b i : ℕ} (hab : a ≤ b) :
    hits a b i = mark a i - mark b i := by
  unfold hits mark
  by_cases ha : a ≤ i <;> by_cases hb : b ≤ i
  · simp [ha, hb, not_lt_of_ge hb]
  · simp [ha, hb, Nat.lt_of_not_ge hb]
  · exact (ha (hab.trans hb)).elim
  · simp [ha, hb]
theorem recover_rectangle {a b c d i j : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    hits a b i * hits c d j =
       mark a i * mark c j - mark b i * mark c j
         - mark a i * mark d j + mark b i * mark d j := by
  rw [recover_range hab, recover_range hcd]
  ring
theorem batched_flux_recovery {E : Type*} (s : Finset E)
    (weight : E → ℤ) (a b c d : E → ℕ) (i j : ℕ)
    (hab : ∀ e ∈ s, a e ≤ b e) (hcd : ∀ e ∈ s, c e ≤ d e) :
    (∑ e ∈ s, weight e * (hits (a e) (b e) i * hits (c e) (d e) j)) =
      ∑ e ∈ s, weight e *
        (mark (a e) i * mark (c e) j - mark (b e) i * mark (c e) j
          - mark (a e) i * mark (d e) j + mark (b e) i * mark (d e) j) := by
  apply Finset.sum_congr rfl
  intro e he
  rw [recover_rectangle (hab e he) (hcd e he)]
end PosetFlux
#print axioms PosetFlux.batched_flux_recovery
