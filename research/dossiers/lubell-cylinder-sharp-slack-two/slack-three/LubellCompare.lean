import Lean.Elab.Tactic.Omega

namespace LubellSlackThree

/-- The scaled top/bottom pair shares its positive symmetric factor. -/
theorem low_ge_high (a b : Int) (ha : 2≤a) (hab : a≤b) :
    (a+1)*(a+b+2)*a ≤ (a+1)*(a+b+2)*b := by
  exact Int.mul_le_mul_of_nonneg_left hab (Int.mul_nonneg (by omega) (by omega))

/-- After cancelling the common positive factor in the exact binomial
    formulas, this inequality says the bottom star beats the cylinder. -/
theorem low_gt_cylinder (a b : Int) (ha : 2≤a) (hab : a≤b) (hb : 3≤b) :
    (a+b)*(a+b+1) < (a+1)*b*(b+1) := by
  by_cases h : 3≤a
  · calc
      _ ≤ (2*b)*(a+b+1) :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      _ < (2*b)*(2*(b+1)) :=
        Int.mul_lt_mul_of_pos_left (by omega) (by omega)
      _ = 4*b*(b+1) := by
        calc
          (2*b)*(2*(b+1)) = ((2*b)*2)*(b+1) := (Int.mul_assoc ..).symm
          _ = (2*(2*b))*(b+1) := by rw [Int.mul_comm (2*b) 2]
          _ = _ := by rw [← Int.mul_assoc 2 2 b]; rfl
      _ ≤ _ := Int.mul_le_mul_of_nonneg_right
        (Int.mul_le_mul_of_nonneg_right (by omega) (by omega)) (by omega)
  · have ha' : a=2 := by omega
    rw [ha']
    have hl : (2+b)*(2+b+1) = b*b+5*b+6 := by
      rw [show 2+b+1=b+3 by omega, Int.add_mul, Int.mul_add, Int.mul_add]
      omega
    have hr : (2+1)*b*(b+1) = 3*(b*b)+3*b := by
      rw [Int.mul_assoc, Int.mul_add, Int.mul_one, Int.mul_add]; rfl
    have hm : 3*b≤b*b := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega

end LubellSlackThree
#print axioms LubellSlackThree.low_ge_high
#print axioms LubellSlackThree.low_gt_cylinder
