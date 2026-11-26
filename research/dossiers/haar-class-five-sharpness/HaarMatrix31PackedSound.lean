import HaarMatrix31Core
import HaarMatrix31Packed
import HaarHalfCollision

namespace HaarMatrix31PackedSound
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open HaarMatrix31Filtration HaarMatrix31Core HaarMatrix31Packed

def project (A : Mat) : Array ℕ := #[(A 0 1).val, (A 0 2).val, (A 0 3).val, (A 0 4).val, (A 0 5).val, (A 1 2).val, (A 1 3).val, (A 1 4).val, (A 1 5).val, (A 2 3).val, (A 2 4).val, (A 2 5).val, (A 3 4).val, (A 3 5).val, (A 4 5).val]

def rawXN : Mat := unflatten #[1,17,29,7,17,10,0,1,9,15,1,17,0,0,1,12,7,26,0,0,0,1,29,28,0,0,0,0,1,17,0,0,0,0,0,1]
def rawYN : Mat := unflatten #[1,3,29,30,24,29,0,1,20,10,8,20,0,0,1,16,19,1,0,0,0,1,7,2,0,0,0,0,1,18,0,0,0,0,0,1]

theorem rawUnit {A : Mat} (h : Band 1 (A-1)) : IsUnit A := by
  simpa only [add_sub_cancel] using unit_add h

theorem val_xn : value HaarMatrix31Core.x⁻¹ = rawXN := by
  have hu : IsUnit rawX := rawUnit gen_band.1
  apply hu.mul_right_inj.mp
  have h := value_mul HaarMatrix31Core.x HaarMatrix31Core.x⁻¹
  rw [mul_inv_cancel, value_x] at h
  change (1 : Mat) = rawX * value HaarMatrix31Core.x⁻¹ at h
  rw [← h]
  decide

theorem val_yn : value HaarMatrix31Core.y⁻¹ = rawYN := by
  have hu : IsUnit rawY := rawUnit gen_band.2
  apply hu.mul_right_inj.mp
  have h := value_mul HaarMatrix31Core.y HaarMatrix31Core.y⁻¹
  rw [mul_inv_cancel, value_y] at h
  change (1 : Mat) = rawY * value HaarMatrix31Core.y⁻¹ at h
  rw [← h]
  decide

theorem diag {A : Mat} (h : Band 1 (A-1)) (i : Fin 6) : A i i = 1 := by
  have hh := h i i (by omega)
  simpa [Matrix.sub_apply] using (sub_eq_zero.mp hh)

theorem below {A : Mat} (h : Band 1 (A-1)) (i j : Fin 6) (hh : j < i) : A i j = 0 := by
  have b := h i j (by omega)
  simpa [Matrix.sub_apply, ne_of_gt hh] using (sub_eq_zero.mp b)

theorem modVal {a : ZMod 31} {n : ℕ} (h : a = (n : ZMod 31)) : a.val = n%31 := by
  rw [h, ZMod.val_natCast]


private theorem eq_xp (A : Mat) (h : Band 1 (A-1)) : project (A*rawX) = xp (project A) := by
  unfold project xp
  simp only [Array.mk.injEq, List.cons.injEq, and_true]
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 14 + (A 0 1 * 1 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 0 + (A 0 1 * 22 + (A 0 2 * 1 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 19 + (A 0 3 * 1 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 0 + (A 0 3 * 2 + (A 0 4 * 1 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 14 + (A 0 5 * 1))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 0 + (A 1 1 * 22 + (A 1 2 * 1 + (A 1 3 * 0 + (A 1 4 * 0 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 19 + (A 1 3 * 1 + (A 1 4 * 0 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 0 + (A 1 3 * 2 + (A 1 4 * 1 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 0 + (A 1 3 * 0 + (A 1 4 * 14 + (A 1 5 * 1))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 19 + (A 2 3 * 1 + (A 2 4 * 0 + (A 2 5 * 0))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 0 + (A 2 3 * 2 + (A 2 4 * 1 + (A 2 5 * 0))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 0 + (A 2 3 * 0 + (A 2 4 * 14 + (A 2 5 * 1))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 3 0 * 0 + (A 3 1 * 0 + (A 3 2 * 0 + (A 3 3 * 2 + (A 3 4 * 1 + (A 3 5 * 0))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 3 0 * 0 + (A 3 1 * 0 + (A 3 2 * 0 + (A 3 3 * 0 + (A 3 4 * 14 + (A 3 5 * 1))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 4 0 * 0 + (A 4 1 * 0 + (A 4 2 * 0 + (A 4 3 * 0 + (A 4 4 * 14 + (A 4 5 * 1))))) = _
    simp only [below h 4 0 (by decide), below h 4 1 (by decide), below h 4 2 (by decide), below h 4 3 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring

private theorem eq_yp (A : Mat) (h : Band 1 (A-1)) : project (A*rawY) = yp (project A) := by
  unfold project yp
  simp only [Array.mk.injEq, List.cons.injEq, and_true]
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 28 + (A 0 1 * 1 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 0 + (A 0 1 * 11 + (A 0 2 * 1 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 15 + (A 0 3 * 1 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 0 + (A 0 3 * 24 + (A 0 4 * 1 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 13 + (A 0 5 * 1))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 0 + (A 1 1 * 11 + (A 1 2 * 1 + (A 1 3 * 0 + (A 1 4 * 0 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 15 + (A 1 3 * 1 + (A 1 4 * 0 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 0 + (A 1 3 * 24 + (A 1 4 * 1 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 0 + (A 1 3 * 0 + (A 1 4 * 13 + (A 1 5 * 1))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 15 + (A 2 3 * 1 + (A 2 4 * 0 + (A 2 5 * 0))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 0 + (A 2 3 * 24 + (A 2 4 * 1 + (A 2 5 * 0))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 0 + (A 2 3 * 0 + (A 2 4 * 13 + (A 2 5 * 1))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 3 0 * 0 + (A 3 1 * 0 + (A 3 2 * 0 + (A 3 3 * 24 + (A 3 4 * 1 + (A 3 5 * 0))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 3 0 * 0 + (A 3 1 * 0 + (A 3 2 * 0 + (A 3 3 * 0 + (A 3 4 * 13 + (A 3 5 * 1))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 4 0 * 0 + (A 4 1 * 0 + (A 4 2 * 0 + (A 4 3 * 0 + (A 4 4 * 13 + (A 4 5 * 1))))) = _
    simp only [below h 4 0 (by decide), below h 4 1 (by decide), below h 4 2 (by decide), below h 4 3 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring

private theorem eq_xn (A : Mat) (h : Band 1 (A-1)) : project (A*rawXN) = xn (project A) := by
  unfold project xn
  simp only [Array.mk.injEq, List.cons.injEq, and_true]
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 17 + (A 0 1 * 1 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 29 + (A 0 1 * 9 + (A 0 2 * 1 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 7 + (A 0 1 * 15 + (A 0 2 * 12 + (A 0 3 * 1 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 17 + (A 0 1 * 1 + (A 0 2 * 7 + (A 0 3 * 29 + (A 0 4 * 1 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 10 + (A 0 1 * 17 + (A 0 2 * 26 + (A 0 3 * 28 + (A 0 4 * 17 + (A 0 5 * 1))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 29 + (A 1 1 * 9 + (A 1 2 * 1 + (A 1 3 * 0 + (A 1 4 * 0 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 7 + (A 1 1 * 15 + (A 1 2 * 12 + (A 1 3 * 1 + (A 1 4 * 0 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 17 + (A 1 1 * 1 + (A 1 2 * 7 + (A 1 3 * 29 + (A 1 4 * 1 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 10 + (A 1 1 * 17 + (A 1 2 * 26 + (A 1 3 * 28 + (A 1 4 * 17 + (A 1 5 * 1))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 7 + (A 2 1 * 15 + (A 2 2 * 12 + (A 2 3 * 1 + (A 2 4 * 0 + (A 2 5 * 0))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 17 + (A 2 1 * 1 + (A 2 2 * 7 + (A 2 3 * 29 + (A 2 4 * 1 + (A 2 5 * 0))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 10 + (A 2 1 * 17 + (A 2 2 * 26 + (A 2 3 * 28 + (A 2 4 * 17 + (A 2 5 * 1))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 3 0 * 17 + (A 3 1 * 1 + (A 3 2 * 7 + (A 3 3 * 29 + (A 3 4 * 1 + (A 3 5 * 0))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 3 0 * 10 + (A 3 1 * 17 + (A 3 2 * 26 + (A 3 3 * 28 + (A 3 4 * 17 + (A 3 5 * 1))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 4 0 * 10 + (A 4 1 * 17 + (A 4 2 * 26 + (A 4 3 * 28 + (A 4 4 * 17 + (A 4 5 * 1))))) = _
    simp only [below h 4 0 (by decide), below h 4 1 (by decide), below h 4 2 (by decide), below h 4 3 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring

private theorem eq_yn (A : Mat) (h : Band 1 (A-1)) : project (A*rawYN) = yn (project A) := by
  unfold project yn
  simp only [Array.mk.injEq, List.cons.injEq, and_true]
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 3 + (A 0 1 * 1 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 29 + (A 0 1 * 20 + (A 0 2 * 1 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 30 + (A 0 1 * 10 + (A 0 2 * 16 + (A 0 3 * 1 + (A 0 4 * 0 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 24 + (A 0 1 * 8 + (A 0 2 * 19 + (A 0 3 * 7 + (A 0 4 * 1 + (A 0 5 * 0))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 0 0 * 29 + (A 0 1 * 20 + (A 0 2 * 1 + (A 0 3 * 2 + (A 0 4 * 18 + (A 0 5 * 1))))) = _
    simp only [diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 29 + (A 1 1 * 20 + (A 1 2 * 1 + (A 1 3 * 0 + (A 1 4 * 0 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 30 + (A 1 1 * 10 + (A 1 2 * 16 + (A 1 3 * 1 + (A 1 4 * 0 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 24 + (A 1 1 * 8 + (A 1 2 * 19 + (A 1 3 * 7 + (A 1 4 * 1 + (A 1 5 * 0))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 1 0 * 29 + (A 1 1 * 20 + (A 1 2 * 1 + (A 1 3 * 2 + (A 1 4 * 18 + (A 1 5 * 1))))) = _
    simp only [below h 1 0 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 30 + (A 2 1 * 10 + (A 2 2 * 16 + (A 2 3 * 1 + (A 2 4 * 0 + (A 2 5 * 0))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 24 + (A 2 1 * 8 + (A 2 2 * 19 + (A 2 3 * 7 + (A 2 4 * 1 + (A 2 5 * 0))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 2 0 * 29 + (A 2 1 * 20 + (A 2 2 * 1 + (A 2 3 * 2 + (A 2 4 * 18 + (A 2 5 * 1))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 3 0 * 24 + (A 3 1 * 8 + (A 3 2 * 19 + (A 3 3 * 7 + (A 3 4 * 1 + (A 3 5 * 0))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 3 0 * 29 + (A 3 1 * 20 + (A 3 2 * 1 + (A 3 3 * 2 + (A 3 4 * 18 + (A 3 5 * 1))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change A 4 0 * 29 + (A 4 1 * 20 + (A 4 2 * 1 + (A 4 3 * 2 + (A 4 4 * 18 + (A 4 5 * 1))))) = _
    simp only [below h 4 0 (by decide), below h 4 1 (by decide), below h 4 2 (by decide), below h 4 3 (by decide), diag h, zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring

theorem project_one : project (value (1 : UT)) = zero := by
  decide

theorem project_step (pos : Bool) (j : Fin 3) (g : UT) :
    project (value (g * (if pos then HaarHalfCollision.port HaarMatrix31Core.x HaarMatrix31Core.y j
      else (HaarHalfCollision.port HaarMatrix31Core.x HaarMatrix31Core.y j)⁻¹))) =
      move pos j.val (project (value g)) := by
  have hg : Band 1 (value g-1) := g.property
  fin_cases j <;> cases pos
  · simpa [HaarHalfCollision.port,move]
  · simpa [HaarHalfCollision.port,move]
  · simpa [HaarHalfCollision.port,move,value_mul,val_xn] using eq_xn (value g) hg
  · simpa [HaarHalfCollision.port,move,value_mul,value_x] using eq_xp (value g) hg
  · simpa [HaarHalfCollision.port,move,value_mul,val_yn] using eq_yn (value g) hg
  · simpa [HaarHalfCollision.port,move,value_mul,value_y] using eq_yp (value g) hg

end HaarMatrix31PackedSound

#print axioms HaarMatrix31PackedSound.project_step
