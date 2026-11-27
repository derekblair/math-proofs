import GeometricGridOperator

namespace RobustFolkman.GeometricGap
open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- For a symmetric perturbation the maximum absolute row sum controls the
operator norm. This converts degree in a disagreement graph into error. -/
theorem symmetric_norm_le_row_sum (A : Matrix J J ℝ) (sym : ∀ i j, A i j=A j i)
    (B : ℝ) (B0 : 0≤B) (row : ∀ i, ∑ j, ‖A i j‖≤B) : ‖A‖≤B := by
  apply real_symmetric_matrix_norm_bound A (by
    ext i j
    simpa only [conjTranspose_apply,star_trivial] using sym j i) B B0
  intro v
  have split (i j : J) : ‖A i j‖*(‖v i‖*‖v j‖) ≤ ‖A i j‖*((v i)^2+(v j)^2)/2 := by
    have h : ‖v i‖*‖v j‖≤((v i)^2+(v j)^2)/2 := by
      have h := sq_nonneg (‖v i‖-‖v j‖)
      simp only [sub_sq,Real.norm_eq_abs,sq_abs] at h
      simp only [Real.norm_eq_abs]
      nlinarith only [h]
    convert mul_le_mul_of_nonneg_left h (norm_nonneg (A i j)) using 1 <;> ring
  have sw : (∑ i, ∑ j, ‖A i j‖*(v j)^2) = ∑ i, ∑ j, ‖A i j‖*(v i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [sym j i]
  calc
    _ ≤ ∑ i, ∑ j, ‖A i j*(v i*v j)‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, ‖A i j‖*((v i)^2+(v j)^2)/2 := by
      simp only [norm_mul]
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => split i j))
    _ = ∑ i, ∑ j, ‖A i j‖*(v i)^2 := by
      simp only [mul_add,add_div,Finset.sum_add_distrib,←Finset.sum_div,sw]
      ring
    _ = ∑ i, (∑ j, ‖A i j‖)*(v i)^2 := by simp only [Finset.sum_mul]
    _ ≤ B*∑ i, (v i)^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (row i) (sq_nonneg _))

#print axioms symmetric_norm_le_row_sum
end RobustFolkman.GeometricGap
