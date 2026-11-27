import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace PermanentUniformPhaseMask

theorem relative_net_slack (e p u eps : ℚ)
    (heps1 : eps ≤ 1)
    (hu : 0 ≤ u) (hsmall : u ≤ eps * p / 8)
    (h : e ≤ eps / 2 * (p + u) + 2 * u) :
    e ≤ eps * p := by
  nlinarith [mul_nonneg (sub_nonneg.mpr heps1) hu]

theorem weight_count {ι : Type*} [Fintype ι]
    (w : ι → ℚ) (cap lower : ℚ) (hcap : ∀ i, w i ≤ cap)
    (hlower : lower ≤ ∑ i, w i) :
    lower ≤ (Fintype.card ι : ℚ) * cap := by
  classical
  calc
    lower ≤ ∑ i, w i := hlower
    _ ≤ ∑ (_ : ι), cap := Finset.sum_le_sum (fun i _ => hcap i)
    _ = _ := by simp

#print axioms relative_net_slack
#print axioms weight_count

end PermanentUniformPhaseMask
