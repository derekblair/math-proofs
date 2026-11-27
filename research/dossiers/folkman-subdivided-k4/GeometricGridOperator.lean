import GeometricGridQuadratic
import GeometricOperatorOrder

namespace RobustFolkman.GeometricGap
open Matrix WithLp Finset
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem real_symmetric_matrix_norm_bound (A : Matrix J J ℝ) (sym : A.IsHermitian)
    (B : ℝ) (B0 : 0≤B)
    (quad : ∀ v : J→ℝ, ‖∑ i, ∑ j, A i j*(v i*v j)‖≤B*∑ i, (v i)^2) :
    ‖A‖≤B := by
  have s : ((Matrix.toEuclideanCLM (n:=J) (𝕜:=ℝ) A) : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J).IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,Matrix.isSymmetric_toEuclideanLin_iff]
    exact sym
  rw [←Matrix.l2_opNorm_toEuclideanCLM,ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ s]
  apply ciSup_le
  intro x
  rw [real_matrix_rayleigh_formula,abs_div,abs_of_nonneg (sq_nonneg ‖x‖)]
  by_cases x0 : x=0
  · simp [x0,B0]
  · have p : 0<‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr x0)
    apply (div_le_iff₀ p).2
    have h := quad (ofLp x)
    rw [←EuclideanSpace.real_norm_sq_eq x] at h
    convert h using 1
    rw [Real.norm_eq_abs]
    congr 1
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

#print axioms real_symmetric_matrix_norm_bound
end RobustFolkman.GeometricGap
