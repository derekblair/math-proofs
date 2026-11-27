import GeometricPage

namespace RobustFolkman.GeometricGap
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Determinant part of transporting orthonormal coordinates to Gram
coordinates. Taking the positive square root fixes the inverse Jacobian. -/
theorem anchor_det_scale (T : Matrix I I ℝ) :
    Real.sqrt (T*T.transpose).det = |T.det| := by
  rw [det_mul,det_transpose,← pow_two,Real.sqrt_sq_eq_abs]

theorem anchor_transpose_inverse (T : Matrix I I ℝ) (d : IsUnit T.det) :
    T.transpose*(T*T.transpose)⁻¹*T=1 := by
  have dt : IsUnit T.transpose.det := by simpa only [det_transpose] using d
  have dp : IsUnit (T*T.transpose).det := by
    rw [det_mul]
    exact d.mul dt
  have L : T.transpose⁻¹*(T.transpose*(T*T.transpose)⁻¹*T)=T.transpose⁻¹ := by
    calc
      _ = (T*T.transpose)⁻¹*T := by
        rw [← Matrix.mul_assoc,← Matrix.mul_assoc,T.transpose.nonsing_inv_mul dt,one_mul]
      _ = (T*T.transpose)⁻¹*(T*T.transpose)*T.transpose⁻¹ := by
        rw [Matrix.mul_assoc,T.transpose.mul_nonsing_inv_cancel_right T dt]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ dp,one_mul]
  have h := congrArg (fun A : Matrix I I ℝ => T.transpose*A) L
  rw [← Matrix.mul_assoc,T.transpose.mul_nonsing_inv dt,one_mul] at h
  exact h

theorem anchor_inverse_norm (T : Matrix I I ℝ) (d : IsUnit T.det) (x : I→ℝ) :
    let y := T *ᵥ x
    y ⬝ᵥ ((T*T.transpose)⁻¹ *ᵥ y) = ∑ i, x i^2 := by
  intro y
  change (T *ᵥ x) ⬝ᵥ ((T*T.transpose)⁻¹ *ᵥ (T *ᵥ x)) = _
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec T x,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,anchor_transpose_inverse T d,
      Matrix.one_mulVec]
  simp [dotProduct,pow_two]

#print axioms anchor_det_scale
#print axioms anchor_inverse_norm
end RobustFolkman.GeometricGap
