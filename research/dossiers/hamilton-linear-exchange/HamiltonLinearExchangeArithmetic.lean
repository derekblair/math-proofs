import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace HamiltonLinearExchange

theorem winding_lower (m D k a : ℕ)
    (ha : 0 < a) (hd : m ∣ a) (h : a ≤ D * k) :
    m ≤ D * k := (Nat.le_of_dvd ha hd).trans h

theorem one_high_step_budget {ι : Type*} [Fintype ι]
    (d : ℕ) (step : ι → ℕ) (high : ι → Bool)
    (hs : ∀ i, step i ≤ d + (if high i then 1 else 0))
    (hh : (∑ i, (if high i then 1 else 0 : ℕ)) ≤ 1) :
    (∑ i, step i) ≤ d * Fintype.card ι + 1 := by
  classical
  calc
    (∑ i, step i) ≤ ∑ i, (d + (if high i then 1 else 0 : ℕ)) :=
      Finset.sum_le_sum (fun i _ => hs i)
    _ = d * Fintype.card ι + (∑ i, (if high i then 1 else 0 : ℕ)) := by
      simp [Finset.sum_add_distrib, Nat.mul_comm]
    _ ≤ _ := Nat.add_le_add_left hh _

theorem multiple_windings_gap (m d : ℚ)
    (hm : 0 ≤ m) (hd : 1 ≤ d) :
    (m - 1) * (d + 1) < (2 * m) * d := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hd) hm]

#print axioms winding_lower
#print axioms one_high_step_budget
#print axioms multiple_windings_gap

end HamiltonLinearExchange
