import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega

namespace Chronology

open scoped BigOperators

/-- n distinct coordinates can be spread over two paths using the same
available phase slots precisely when there is room for ceil(n/2) slots. -/
theorem split_sameSlots (n slots : ℕ) :
    (∃ a b : ℕ, a+b=n ∧ a≤slots ∧ b≤slots) ↔ (n+1)/2 ≤ slots := by
  constructor
  · rintro ⟨a,b,e,ha,hb⟩
    omega
  · intro h
    exact ⟨n/2,(n+1)/2,by omega,by omega,h⟩

/-- An odd occupied phase consumes a slot even if a different phase also has
an odd count: global rounding is not a substitute for per-phase rounding. -/
theorem oddPhases_example :
    (1+1 ≤ 2*1) ∧ ¬ (((1+1)/2 + (1+1)/2 : ℕ) ≤ 1) := by decide

theorem globalSlotBudget {k : ℕ} (needed cap : Fin k → ℕ) (Q : ℕ) :
    (∃ slot : Fin k → ℕ, (∀ i, (needed i+1)/2 ≤ slot i ∧ slot i ≤ cap i) ∧
      (∑ i, slot i) ≤ Q) ↔
    (∀ i, (needed i+1)/2 ≤ cap i) ∧ (∑ i, (needed i+1)/2) ≤ Q := by
  constructor
  · rintro ⟨slot,hs,ht⟩
    refine ⟨fun i => (hs i).1.trans (hs i).2, ?_⟩
    exact (Finset.sum_le_sum (fun i _ => (hs i).1)).trans ht
  · rintro ⟨hc,hq⟩
    exact ⟨fun i => (needed i+1)/2, fun i => ⟨le_rfl,hc i⟩, hq⟩

/-- Large priority weight ensures that covering one more clone dominates
every possible gain in real-label objective. -/
theorem saturationWins (n c C score : ℕ) (lt : c < C) (cap : score ≤ n) :
    (n+1)*c+score < (n+1)*C := by
  have h := Nat.mul_le_mul_left (n+1) (Nat.succ_le_of_lt lt)
  rw [Nat.mul_succ] at h
  omega

#print axioms saturationWins
#print axioms globalSlotBudget
#print axioms split_sameSlots
#print axioms oddPhases_example
end Chronology
