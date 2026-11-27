import GeometricRankOneVariance
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace RobustFolkman.GeometricGap
open Matrix WithLp Finset
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem real_matrix_rayleigh_formula (A : Matrix J J ℝ) (x : EuclideanSpace ℝ J) :
    (toEuclideanCLM (n:=J) (𝕜:=ℝ) A).rayleighQuotient x = (ofLp x ⬝ᵥ (A*ᵥofLp x))/‖x‖^2 := by
  unfold ContinuousLinearMap.rayleighQuotient
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  change ⟪toEuclideanCLM (n:=J) (𝕜:=ℝ) A x,x⟫_ℝ / ‖x‖^2=_
  rw [real_inner_comm,Matrix.inner_toEuclideanCLM]

/-- Euclidean operator norm is monotone between positive semidefinite
real matrices. The right matrix is positive automatically. -/
theorem real_matrix_operator_mono (A B : Matrix J J ℝ) (a : A.PosSemidef)
    (h : (B-A).PosSemidef) : ‖A‖≤‖B‖ := by
  have sym : ((Matrix.toEuclideanCLM (n:=J) (𝕜:=ℝ) A) : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J).IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,Matrix.isSymmetric_toEuclideanLin_iff]
    exact a.isHermitian
  rw [←Matrix.l2_opNorm_toEuclideanCLM, ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ sym]
  apply ciSup_le
  intro x
  rw [real_matrix_rayleigh_formula]
  have aa : 0≤ofLp x ⬝ᵥ (A *ᵥ ofLp x) := by simpa only [star_trivial] using a.dotProduct_mulVec_nonneg (ofLp x)
  have bb : 0≤ofLp x ⬝ᵥ ((B-A)*ᵥofLp x) := by simpa only [star_trivial] using h.dotProduct_mulVec_nonneg (ofLp x)
  rw [Matrix.sub_mulVec,dotProduct_sub,sub_nonneg] at bb
  rw [abs_of_nonneg (div_nonneg aa (sq_nonneg _))]
  refine (div_le_div_of_nonneg_right bb (sq_nonneg _)).trans ?_
  rw [←real_matrix_rayleigh_formula,←Matrix.l2_opNorm_toEuclideanCLM]
  exact (le_abs_self _).trans (ContinuousLinearMap.rayleighQuotient_le_norm _ x)

theorem rankOneMat_operator_bound (v : J→ℝ) :
    ‖rankOneMat v‖ ≤ ∑ j, (v j)^2 := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM]
  let V := toLp 2 v
  have en : (∑ j, (v j)^2)=‖V‖^2 := (EuclideanSpace.real_norm_sq_eq V).symm
  rw [en]
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro x
  have eq : Matrix.toEuclideanCLM (n:=J) (𝕜:=ℝ) (rankOneMat v) x = (v ⬝ᵥ ofLp x) • V := by
    apply WithLp.ofLp_injective
    rw [Matrix.ofLp_toEuclideanCLM,rankOneMat,Matrix.vecMulVec_mulVec,op_smul_eq_smul]
    rfl
  rw [eq,norm_smul,Real.norm_eq_abs]
  have e : v ⬝ᵥ ofLp x = ⟪x,V⟫_ℝ := by
    simp [V,PiLp.inner_apply,dotProduct,RCLike.inner_apply, mul_comm]
  rw [e]
  have h := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm x V) (norm_nonneg V)
  nlinarith only [h]

theorem weighted_rank_one_variance_norm {I : Type*} [Fintype I]
    (w : I→ℝ) (v : I→J→ℝ) (K : ℝ) (K0 : 0≤K)
    (w0 : ∀ i, 0≤w i) (w1 : ∑ i,w i=1) (bound : ∀ i, ∑ j, (v i j)^2≤K) :
    let C := fun i => rankOneMat (v i)
    let M := weightedMatrix w C
    ‖weightedMatrix w (fun i => (C i-M)^2)‖ ≤ K*‖M‖ := by
  intro C M
  have h := weighted_rank_one_variance w v K w0 w1 bound
  have b := real_matrix_operator_mono _ _ h.1 h.2
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg K0] at b
  exact b

#print axioms weighted_rank_one_variance_norm
#print axioms rankOneMat_operator_bound
end RobustFolkman.GeometricGap
