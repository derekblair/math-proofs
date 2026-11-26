import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace Availability

variable {F : Type*} [Field F]

/-- Change of normalization from a nonzero repaired point to the held secret
is injective in the (nonzero) helper point. -/
theorem lagrange_ratio_ne (a u v C : F) (ha : a ≠ 0) (hu : u ≠ 0)
    (hv : v ≠ 0) (hc : C ≠ 0) (h : u ≠ v) :
    C * ((a-u)/(0-u)) ≠ C * ((a-v)/(0-v)) := by
  intro H
  have E := mul_left_cancel₀ hc H
  simp only [zero_sub] at E
  have eu : -u ≠ 0 := neg_ne_zero.mpr hu
  have ev : -v ≠ 0 := neg_ne_zero.mpr hv
  field_simp [eu,ev] at E
  apply h
  have Q : a * (u-v) = 0 := by
    linear_combination E
  exact sub_eq_zero.mp ((mul_eq_zero.mp Q).resolve_left ha)

/-- Equal and opposite helper changes preserve the repair sum and can
produce any prescribed shift of the secret if the two ratios differ. -/
theorem edge_shift (u v delta : F) (hne : u ≠ v) :
    ∃ r : F, r+(-r)=0 ∧ u*r+v*(-r)=delta := by
  refine ⟨delta/(u-v), by simp, ?_⟩
  rw [mul_neg, ← sub_eq_add_neg, ← sub_mul]
  field_simp [sub_ne_zero.mpr hne]

theorem extra_read_shift (a b c d delta : F) (hne : a*d-b*c ≠ 0) :
    ∃ x y : F, c*x+d*y=0 ∧ a*x+b*y=delta := by
  let r := delta/(a*d-b*c)
  refine ⟨d*r,-c*r,?_,?_⟩
  · ring
  · calc
      a*(d*r)+b*(-c*r) = (a*d-b*c)*r := by ring
      _ = delta := by dsimp [r]; field_simp [hne]

#print axioms extra_read_shift
#print axioms lagrange_ratio_ne
#print axioms edge_shift
end Availability
