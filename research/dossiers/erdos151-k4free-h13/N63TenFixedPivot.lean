import N63TenPrice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Erdos151N63
open scoped BigOperators

set_option maxHeartbeats 0

theorem failure_unit : ∀ d t a : Fin 9,
    4≤d.val → d.val≠5 → 2≤t.val → t.val≤d.val → a.val<9-d.val →
    (minCenter d.val t.val ≠ 99 → alphaFloor (9-d.val-1-a.val) < minCenter d.val t.val) →
    2*t.val ≤ a.val + (if d.val=4 then 4 else 5) := by decide +kernel

/-- In a ten-link with maximum degree 4,6,7 or 8, a fixed
maximum pivot has a safe partner certified by the elementary
triangle-free center-pool sizes.  Only degree-sum data is needed. -/
theorem fixed_pivot_except_five (d q : Nat) (hq : d+q=9)
    (hd : 4≤d) (hd' : d≤8) (h5 : d≠5) (deg right : Fin q → Nat)
    (range : ∀ y, 2 ≤ deg y ∧ deg y ≤ d)
    (inside : ∀ y, right y < q)
    (dense : 30 + (∑ y : Fin q, right y) ≤ 2*d+2*(∑ y : Fin q, deg y)) :
    ∃ y, minCenter d (deg y) ≠ 99 ∧
      minCenter d (deg y) ≤ alphaFloor (q-1-right y) := by
  by_contra! h
  have bound (y : Fin q) : 2*deg y ≤ right y + (if d=4 then 4 else 5) := by
    have hi := inside y
    have hh := range y
    have qe : 9-d=q := by omega
    have hh' := failure_unit ⟨d,by omega⟩ ⟨deg y,by omega⟩ ⟨right y,by omega⟩
      hd h5 hh.1 hh.2 (by change right y < 9-d; omega)
    simpa [qe] using hh' (by simpa [qe] using h y)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun y _ => bound y)
  simp only [←Finset.mul_sum, Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  by_cases h4 : d=4
  · simp [h4] at hs
    omega
  · simp [h4] at hs
    omega

#print axioms fixed_pivot_except_five
end Erdos151N63
