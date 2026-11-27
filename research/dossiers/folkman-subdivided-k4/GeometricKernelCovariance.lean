import GeometricColumnGram

namespace RobustFolkman.GeometricGap
open Matrix Finset
open scoped Matrix.Norms.L2Operator
variable {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I] [DecidableEq I]

noncomputable def kernelFeature (K : Ω→Ω→ℝ) (p : Ω→ℝ) (x : Ω) (j : Ω) : ℝ :=
  K x j * Real.sqrt (p j)

noncomputable def weightedKernel (K : Ω→Ω→ℝ) (p : Ω→ℝ) : Matrix Ω Ω ℝ :=
  Matrix.of fun x j => Real.sqrt (p x) * kernelFeature K p x j

theorem kernel_feature_population_gram (K : Ω→Ω→ℝ) (p : Ω→ℝ)
    (p0 : ∀ j, 0≤p j) :
    weightedMatrix p (fun x => rankOneMat (kernelFeature K p x)) =
      (weightedKernel K p)ᴴ * weightedKernel K p := by
  ext i j
  simp only [weightedMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    rankOneMat,Matrix.vecMulVec_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    star_trivial,weightedKernel,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro x _
  have h := Real.sq_sqrt (p0 x)
  nlinarith only [congrArg (fun k : ℝ => k*kernelFeature K p x i*kernelFeature K p x j) h]

theorem kernel_feature_population_norm (K : Ω→Ω→ℝ) (p : Ω→ℝ)
    (p0 : ∀ j, 0≤p j) :
    ‖weightedMatrix p (fun x => rankOneMat (kernelFeature K p x))‖ =
      ‖weightedKernel K p‖^2 := by
  rw [kernel_feature_population_gram K p p0, Matrix.l2_opNorm_conjTranspose_mul_self,pow_two]

noncomputable def leftFeatureMatrix (K : Ω→Ω→ℝ) (p : Ω→ℝ) (x : I→Ω) : Matrix I Ω ℝ :=
  Matrix.of fun i j => kernelFeature K p (x i) j

def rightColumn (K : Ω→Ω→ℝ) (x : I→Ω) (y : Ω) : I→ℝ :=
  fun i => K (x i) y

theorem right_column_covariance (K : Ω→Ω→ℝ) (p : Ω→ℝ) (x : I→Ω)
    (p0 : ∀ j, 0≤p j) :
    weightedMatrix p (fun y => rankOneMat (rightColumn K x y)) =
      leftFeatureMatrix K p x * (leftFeatureMatrix K p x)ᴴ := by
  ext i j
  simp only [weightedMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    rankOneMat,Matrix.vecMulVec_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    star_trivial,leftFeatureMatrix,Matrix.of_apply,kernelFeature,rightColumn]
  apply Finset.sum_congr rfl
  intro y _
  have h := Real.sq_sqrt (p0 y)
  nlinarith only [congrArg (fun k : ℝ => k*K (x i) y*K (x j) y) h]

theorem left_feature_gram (K : Ω→Ω→ℝ) (p : Ω→ℝ) (x : I→Ω) :
    ∑ i, rankOneMat (kernelFeature K p (x i)) =
      (leftFeatureMatrix K p x)ᴴ * leftFeatureMatrix K p x := by
  ext j k
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply, leftFeatureMatrix,
    rankOneMat,Matrix.vecMulVec_apply,Matrix.sum_apply]

/-- Once the first covariance is bounded, the second matrix Bernstein
step has exactly the same covariance norm before truncation. -/
theorem right_covariance_norm_is_left_sample_covariance (K : Ω→Ω→ℝ) (p : Ω→ℝ) (x : I→Ω)
    (p0 : ∀ j, 0≤p j) :
    ‖weightedMatrix p (fun y => rankOneMat (rightColumn K x y))‖ =
      ‖∑ i, rankOneMat (kernelFeature K p (x i))‖ := by
  rw [right_column_covariance K p x p0,left_feature_gram,Matrix.l2_opNorm_conjTranspose_mul_self]
  let F := leftFeatureMatrix K p x
  have h := Matrix.l2_opNorm_conjTranspose_mul_self Fᴴ
  simpa only [Matrix.conjTranspose_conjTranspose,Matrix.l2_opNorm_conjTranspose,F] using h

/-- Zero truncation cannot increase the operator norm of the column
covariance. It is sufficient to check a deterministic bound on
the squared lengths of the truncated columns. -/
theorem truncate_right_covariance (K : Ω→Ω→ℝ) (p : Ω→ℝ) (x : I→Ω)
    (p0 : ∀ j, 0≤p j) (good : Ω→Bool) :
    ‖weightedMatrix p (fun y => rankOneMat (if good y then rightColumn K x y else 0))‖ ≤
      ‖∑ i, rankOneMat (kernelFeature K p (x i))‖ := by
  rw [←right_covariance_norm_is_left_sample_covariance K p x p0]
  apply real_matrix_operator_mono _ _
  · exact weightedMatrix_psd _ _ p0 (fun j => rankOneMat_psd _)
  · have eq : weightedMatrix p (fun y => rankOneMat (rightColumn K x y)) -
        weightedMatrix p (fun y => rankOneMat (if good y then rightColumn K x y else 0)) =
        weightedMatrix p (fun y => rankOneMat (rightColumn K x y) -
          rankOneMat (if good y then rightColumn K x y else 0)) := by
      simp only [weightedMatrix,smul_sub,Finset.sum_sub_distrib]
    rw [eq]
    apply weightedMatrix_psd _ _ p0
    intro y
    cases h : good y
    · have z : rankOneMat (0:I→ℝ)=0 := by ext i j; simp [rankOneMat,Matrix.vecMulVec_apply]
      simpa only [h, Bool.false_eq_true, if_false,z,sub_zero] using rankOneMat_psd (rightColumn K x y)
    · simpa [h] using (Matrix.PosSemidef.zero : (0 : Matrix I I ℝ).PosSemidef)

#print axioms kernel_feature_population_norm
#print axioms truncate_right_covariance
end RobustFolkman.GeometricGap
