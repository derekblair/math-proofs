import GeometricOperatorOrder

namespace RobustFolkman.GeometricGap
open Matrix Finset
open scoped Matrix.Norms.L2Operator
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem column_gram_rank_one (A : Matrix I J ℝ) :
    A*Aᴴ = ∑ j, rankOneMat (fun i => A i j) := by
  ext i k
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,rankOneMat,Matrix.sum_apply,Matrix.vecMulVec_apply]

theorem column_gram_norm_square (A : Matrix I J ℝ) :
    ‖∑ j, rankOneMat (fun i => A i j)‖ = ‖A‖^2 := by
  rw [←column_gram_rank_one A]
  have h := Matrix.l2_opNorm_conjTranspose_mul_self Aᴴ
  rw [Matrix.conjTranspose_conjTranspose,Matrix.l2_opNorm_conjTranspose] at h
  simpa [pow_two] using h

theorem columns_norm_bound (A : Matrix I J ℝ) (B : ℝ) (B0 : 0≤B)
    (b : ‖∑ j, rankOneMat (fun i => A i j)‖≤B^2) : ‖A‖≤B := by
  rw [column_gram_norm_square] at b
  exact (sq_le_sq₀ (norm_nonneg _) B0).1 b

#print axioms columns_norm_bound
end RobustFolkman.GeometricGap
