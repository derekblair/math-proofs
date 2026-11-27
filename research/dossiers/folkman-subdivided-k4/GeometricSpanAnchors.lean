import GeometricSpanProjection
import GeometricAnchorDensity

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp Matrix
open scoped ENNReal InnerProductSpace
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def spanAnchorMatrix (K : Submodule ℝ E) (b : OrthonormalBasis I ℝ K)
    (v : I→K) : Matrix I I ℝ := fun i j => b.repr (v i) j

theorem spanAnchorMatrix_gram (K : Submodule ℝ E) (b : OrthonormalBasis I ℝ K) (v : I→K) :
    spanAnchorMatrix K b v * (spanAnchorMatrix K b v).transpose =
      fun i j => ⟪(v i:E),(v j:E)⟫_ℝ := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,spanAnchorMatrix,b.repr_apply_apply]
  have h := b.sum_inner_mul_inner (v i) (v j)
  simp_rw [← real_inner_comm (v i)] at h
  exact h.trans (real_inner_comm _ _)

theorem spanAnchorMatrix_isUnit (K : Submodule ℝ E) (b : OrthonormalBasis I ℝ K)
    (v : I→K) (ind : LinearIndependent ℝ v) :
    IsUnit (spanAnchorMatrix K b v).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  let e : K ≃ₗ[ℝ] (I→ℝ) :=
    b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (I→ℝ))
  change LinearIndependent ℝ (e ∘ v)
  exact ind.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)

theorem spanAnchorMatrix_apply (K : Submodule ℝ E) (b : OrthonormalBasis I ℝ K)
    (v : I→K) (x : E) :
    (spanAnchorMatrix K b v) *ᵥ (fun j => ⟪((b j:K):E),x⟫_ℝ) =
    fun i => ⟪(v i:E),x⟫_ℝ := by
  funext i
  change ∑ j, b.repr (v i) j * ⟪((b j:K):E),x⟫_ℝ = _
  simp_rw [b.repr_apply_apply, ← K.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have h := b.sum_inner_mul_inner (v i) (K.orthogonalProjectionOnto x)
  simp_rw [← real_inner_comm (v i)] at h
  exact h.trans (real_inner_comm _ _)

#print axioms spanAnchorMatrix_gram
#print axioms spanAnchorMatrix_apply
end RobustFolkman.GeometricGap
