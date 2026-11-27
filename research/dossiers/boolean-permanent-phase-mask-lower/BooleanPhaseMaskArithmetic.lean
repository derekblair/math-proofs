import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace BooleanPhaseMask

theorem alphabet_cauchy {ι : Type*} [Fintype ι] (p : ι → ℚ)
    (h : (∑ i, p i) = 1) :
    1 ≤ (Fintype.card ι : ℚ) * ∑ i, (p i)^2 := by
  classical
  have hp := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℚ)) p
  simpa [h] using hp

theorem pairing_factor_step (k : ℕ) :
    (2*k+1) * 4^(k+1) * Nat.centralBinom k =
      2*(k+1) * 4^k * Nat.centralBinom (k+1) := by
  calc
    _ = (2*4^k) * (2*(2*k+1) * Nat.centralBinom k) := by rw [pow_succ]; ring
    _ = (2*4^k) * ((k+1) * Nat.centralBinom (k+1)) := by
      rw [← Nat.succ_mul_centralBinom_succ]
    _ = _ := by ring

theorem finite_cover_budget {ι : Type*} [Fintype ι]
    (p : ι → ℚ) (cap : ℚ) (h : ∀ i, p i ≤ cap)
    (hcover : 1 ≤ ∑ i, p i) :
    1 ≤ (Fintype.card ι : ℚ) * cap := by
  classical
  calc
    1 ≤ ∑ i, p i := hcover
    _ ≤ ∑ (_ : ι), cap := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

#print axioms alphabet_cauchy
#print axioms pairing_factor_step
#print axioms finite_cover_budget

end BooleanPhaseMask
