import Ribbon5Packed
import Ribbon5UT

namespace Ribbon5Packed
open HaarMatrixFiltration HaarMatrixCycle Ribbon5UT HaarMatrixPackedSound
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

private theorem proj_aPos (A : Mat) (h : Band 1 (A-1)) :
    project (A*rawA) = aPos (project A) := by
  unfold project aPos
  simp only [Array.mk.injEq,List.cons.injEq,and_true]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 4 + (A 0 1 * 1 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 0 + (A 0 1 * 4 + (A 0 2 * 1 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 4 + (A 0 3 * 1 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 0 + (A 0 3 * 10 + (A 0 4 * 1 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 7 + (A 0 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 0 + (A 1 1 * 4 + (A 1 2 * 1 + (A 1 3 * 0 + (A 1 4 * 0 + (A 1 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 4 + (A 1 3 * 1 + (A 1 4 * 0 + (A 1 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 0 + (A 1 3 * 10 + (A 1 4 * 1 + (A 1 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 0 + (A 1 3 * 0 + (A 1 4 * 7 + (A 1 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 4 + (A 2 3 * 1 + (A 2 4 * 0 + (A 2 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 0 + (A 2 3 * 10 + (A 2 4 * 1 + (A 2 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 0 + (A 2 3 * 0 + (A 2 4 * 7 + (A 2 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 3 0 * 0 + (A 3 1 * 0 + (A 3 2 * 0 + (A 3 3 * 10 + (A 3 4 * 1 + (A 3 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 3 0 * 0 + (A 3 1 * 0 + (A 3 2 * 0 + (A 3 3 * 0 + (A 3 4 * 7 + (A 3 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 4 0 * 0 + (A 4 1 * 0 + (A 4 2 * 0 + (A 4 3 * 0 + (A 4 4 * 7 + (A 4 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
private theorem proj_aNeg (A : Mat) (h : Band 1 (A-1)) :
    project (A*rawAi) = aNeg (project A) := by
  unfold project aNeg
  simp only [Array.mk.injEq,List.cons.injEq,and_true]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 13 + (A 0 1 * 1 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 16 + (A 0 1 * 13 + (A 0 2 * 1 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 4 + (A 0 1 * 16 + (A 0 2 * 13 + (A 0 3 * 1 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 11 + (A 0 1 * 10 + (A 0 2 * 6 + (A 0 3 * 7 + (A 0 4 * 1 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 8 + (A 0 1 * 15 + (A 0 2 * 9 + (A 0 3 * 2 + (A 0 4 * 10 + (A 0 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 16 + (A 1 1 * 13 + (A 1 2 * 1 + (A 1 3 * 0 + (A 1 4 * 0 + (A 1 5 * 0)))))) = _
    simp only [below h 1 0 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 4 + (A 1 1 * 16 + (A 1 2 * 13 + (A 1 3 * 1 + (A 1 4 * 0 + (A 1 5 * 0)))))) = _
    simp only [below h 1 0 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 11 + (A 1 1 * 10 + (A 1 2 * 6 + (A 1 3 * 7 + (A 1 4 * 1 + (A 1 5 * 0)))))) = _
    simp only [below h 1 0 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 8 + (A 1 1 * 15 + (A 1 2 * 9 + (A 1 3 * 2 + (A 1 4 * 10 + (A 1 5 * 1)))))) = _
    simp only [below h 1 0 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 4 + (A 2 1 * 16 + (A 2 2 * 13 + (A 2 3 * 1 + (A 2 4 * 0 + (A 2 5 * 0)))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 11 + (A 2 1 * 10 + (A 2 2 * 6 + (A 2 3 * 7 + (A 2 4 * 1 + (A 2 5 * 0)))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 8 + (A 2 1 * 15 + (A 2 2 * 9 + (A 2 3 * 2 + (A 2 4 * 10 + (A 2 5 * 1)))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 3 0 * 11 + (A 3 1 * 10 + (A 3 2 * 6 + (A 3 3 * 7 + (A 3 4 * 1 + (A 3 5 * 0)))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 3 0 * 8 + (A 3 1 * 15 + (A 3 2 * 9 + (A 3 3 * 2 + (A 3 4 * 10 + (A 3 5 * 1)))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 4 0 * 8 + (A 4 1 * 15 + (A 4 2 * 9 + (A 4 3 * 2 + (A 4 4 * 10 + (A 4 5 * 1)))))) = _
    simp only [below h 4 0 (by decide), below h 4 1 (by decide), below h 4 2 (by decide), below h 4 3 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
private theorem proj_bPos (A : Mat) (h : Band 1 (A-1)) :
    project (A*rawB) = bPos (project A) := by
  unfold project bPos
  simp only [Array.mk.injEq,List.cons.injEq,and_true]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 12 + (A 0 1 * 1 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 0 + (A 0 1 * 12 + (A 0 2 * 1 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 9 + (A 0 3 * 1 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 0 + (A 0 3 * 12 + (A 0 4 * 1 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 0 + (A 0 1 * 0 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 2 + (A 0 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 0 + (A 1 1 * 12 + (A 1 2 * 1 + (A 1 3 * 0 + (A 1 4 * 0 + (A 1 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 9 + (A 1 3 * 1 + (A 1 4 * 0 + (A 1 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 0 + (A 1 3 * 12 + (A 1 4 * 1 + (A 1 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 0 + (A 1 1 * 0 + (A 1 2 * 0 + (A 1 3 * 0 + (A 1 4 * 2 + (A 1 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 9 + (A 2 3 * 1 + (A 2 4 * 0 + (A 2 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 0 + (A 2 3 * 12 + (A 2 4 * 1 + (A 2 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 0 + (A 2 1 * 0 + (A 2 2 * 0 + (A 2 3 * 0 + (A 2 4 * 2 + (A 2 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 3 0 * 0 + (A 3 1 * 0 + (A 3 2 * 0 + (A 3 3 * 12 + (A 3 4 * 1 + (A 3 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 3 0 * 0 + (A 3 1 * 0 + (A 3 2 * 0 + (A 3 3 * 0 + (A 3 4 * 2 + (A 3 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 4 0 * 0 + (A 4 1 * 0 + (A 4 2 * 0 + (A 4 3 * 0 + (A 4 4 * 2 + (A 4 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
private theorem proj_bNeg (A : Mat) (h : Band 1 (A-1)) :
    project (A*rawBi) = bNeg (project A) := by
  unfold project bNeg
  simp only [Array.mk.injEq,List.cons.injEq,and_true]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 5 + (A 0 1 * 1 + (A 0 2 * 0 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 8 + (A 0 1 * 5 + (A 0 2 * 1 + (A 0 3 * 0 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 13 + (A 0 1 * 6 + (A 0 2 * 8 + (A 0 3 * 1 + (A 0 4 * 0 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 14 + (A 0 1 * 13 + (A 0 2 * 6 + (A 0 3 * 5 + (A 0 4 * 1 + (A 0 5 * 0)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 0 0 * 6 + (A 0 1 * 8 + (A 0 2 * 5 + (A 0 3 * 7 + (A 0 4 * 15 + (A 0 5 * 1)))))) = _
    simp only [diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 8 + (A 1 1 * 5 + (A 1 2 * 1 + (A 1 3 * 0 + (A 1 4 * 0 + (A 1 5 * 0)))))) = _
    simp only [below h 1 0 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 13 + (A 1 1 * 6 + (A 1 2 * 8 + (A 1 3 * 1 + (A 1 4 * 0 + (A 1 5 * 0)))))) = _
    simp only [below h 1 0 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 14 + (A 1 1 * 13 + (A 1 2 * 6 + (A 1 3 * 5 + (A 1 4 * 1 + (A 1 5 * 0)))))) = _
    simp only [below h 1 0 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 1 0 * 6 + (A 1 1 * 8 + (A 1 2 * 5 + (A 1 3 * 7 + (A 1 4 * 15 + (A 1 5 * 1)))))) = _
    simp only [below h 1 0 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 13 + (A 2 1 * 6 + (A 2 2 * 8 + (A 2 3 * 1 + (A 2 4 * 0 + (A 2 5 * 0)))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 14 + (A 2 1 * 13 + (A 2 2 * 6 + (A 2 3 * 5 + (A 2 4 * 1 + (A 2 5 * 0)))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 2 0 * 6 + (A 2 1 * 8 + (A 2 2 * 5 + (A 2 3 * 7 + (A 2 4 * 15 + (A 2 5 * 1)))))) = _
    simp only [below h 2 0 (by decide), below h 2 1 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 3 0 * 14 + (A 3 1 * 13 + (A 3 2 * 6 + (A 3 3 * 5 + (A 3 4 * 1 + (A 3 5 * 0)))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 3 0 * 6 + (A 3 1 * 8 + (A 3 2 * 5 + (A 3 3 * 7 + (A 3 4 * 15 + (A 3 5 * 1)))))) = _
    simp only [below h 3 0 (by decide), below h 3 1 (by decide), below h 3 2 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring
  · apply modVal
    simp only [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (A 4 0 * 6 + (A 4 1 * 8 + (A 4 2 * 5 + (A 4 3 * 7 + (A 4 4 * 15 + (A 4 5 * 1)))))) = _
    simp only [below h 4 0 (by decide), below h 4 1 (by decide), below h 4 2 (by decide), below h 4 3 (by decide), diag h,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero]
    push_cast [ZMod.natCast_zmod_val] <;> ring

noncomputable def actualStep (s : V) (j : Fin 3) : V :=
  if j=2 then (!s.1,s.2)
  else (s.1,s.2*(if s.1 then (if j=0 then b else b⁻¹) else (if j=0 then a else a⁻¹)))

def projection (s : V) : State := (s.1,project (value s.2))

@[simp] theorem proj_zero (br : Bool) : projection (br,1) = zero br := by
  apply Prod.ext rfl
  change project (1:Mat)=Array.replicate 15 0
  decide +kernel

theorem step_sound (s : V) (j : Fin 3) : projection (actualStep s j)=step (projection s) j := by
  obtain ⟨side,g⟩ := s
  have B : Band 1 (value g-1) := g.property
  cases side <;> fin_cases j <;>
    simp [actualStep,step,projection,value_mul,val_a,val_ai,val_b,val_bi,
      proj_aPos (value g) B,proj_aNeg (value g) B,proj_bPos (value g) B,proj_bNeg (value g) B]

end Ribbon5Packed
#print axioms Ribbon5Packed.step_sound
