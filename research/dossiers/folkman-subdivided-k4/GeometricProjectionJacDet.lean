import GeometricPage

namespace RobustFolkman.GeometricGap
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Algebraic determinant of the split-polar derivative at a point where
the residual radial direction has coordinate s. Rows and columns are
ordered with the radial coordinate last. -/
theorem projection_jacobian_det (x : I→ℝ) (r s : ℝ) (s0 : s ≠ 0)
    (unit : (∑ i, x i ^ 2)+s^2=1) :
    (Matrix.fromBlocks (r • (1 : Matrix I I ℝ)) (pageCol x)
      (fun (_ : Unit) i => -(r/s)*x i) (fun (_ _ : Unit) => s)).det =
      r^(Fintype.card I)/s := by
  let A : Matrix I I ℝ := r • 1
  let B := pageCol x
  let C : Matrix Unit I ℝ := fun _ i => -(r/s)*x i
  let D : Matrix Unit Unit ℝ := fun _ _ => s
  let U : Matrix Unit Unit ℝ := fun _ _ => 1/s
  let K : Matrix Unit I ℝ := fun _ i => x i/s
  let L := Matrix.fromBlocks (1 : Matrix I I ℝ) (0 : Matrix I Unit ℝ) K 1
  have ld : L.det=1 := by
    simp [L]
  have ka : K*A+C=0 := by
    ext i j
    rw [show K*A=r • K by simp [A, Matrix.mul_smul]]
    change r*(x j/s)+ -(r/s)*x j=0
    field_simp
    <;> ring
  have kb : K*B+D=U := by
    ext i j
    change (∑ k : I, x k/s*x k)+s=1/s
    have sum : (∑ k : I, x k/s*x k) = (∑ k : I, x k^2)/s := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [sum]
    apply (eq_div_iff s0).mpr
    have h : ((∑ i, x i^2)/s+s)*s = (∑ i, x i^2)+s^2 := by
      field_simp
      <;> ring
    rw [h,unit]
  have elim : L * Matrix.fromBlocks A B C D =
      Matrix.fromBlocks A B (0 : Matrix Unit I ℝ) U := by
    unfold L
    rw [Matrix.fromBlocks_multiply]
    simp [ka,kb]
  change (Matrix.fromBlocks A B C D).det = _
  rw [← one_mul (Matrix.fromBlocks A B C D).det, ← ld, ← Matrix.det_mul,elim,
    Matrix.det_fromBlocks_zero₂₁,Matrix.det_unique U]
  simp [A,U,Matrix.det_smul,div_eq_mul_inv]

#print axioms projection_jacobian_det
end RobustFolkman.GeometricGap
