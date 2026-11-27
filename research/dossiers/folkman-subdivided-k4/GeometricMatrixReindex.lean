import GeometricOperatorOrder

namespace RobustFolkman.GeometricGap
open Matrix WithLp Finset
open scoped BigOperators Matrix.Norms.L2Operator
variable {I J U V : Type*} [Fintype I] [Fintype J] [Fintype U] [Fintype V]
    [DecidableEq I] [DecidableEq J] [DecidableEq U] [DecidableEq V]

theorem rectangular_reindex_le (A : Matrix I J ℝ) (e : U≃I) (f : V≃J) :
    ‖A.submatrix e f‖≤‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  let P := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ f
  let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm
  have a : ((Matrix.toEuclideanLin (n:=V) (m:=U) (𝕜:=ℝ)).trans LinearMap.toContinuousLinearMap)
      (A.submatrix e f) x = Q (toLp 2 (A *ᵥ ofLp (P x))) := by
    apply WithLp.ofLp_injective
    funext u
    change (A.submatrix e f *ᵥ ofLp x) u=(A *ᵥ ofLp (P x)) (e u)
    simp only [Matrix.mulVec,dotProduct,Matrix.submatrix_apply]
    calc
      _ = ∑ v : V, A (e u) (f v) * ofLp (P x) (f v) := by
        apply Finset.sum_congr rfl
        intro v _
        change A (e u) (f v) * ofLp x v = A (e u) (f v) * ofLp x (f.symm (f v))
        rw [f.symm_apply_apply]
      _ = _ := f.sum_comp (fun j => A (e u) j * ofLp (P x) j)
  rw [a,Q.norm_map]
  exact (Matrix.l2_opNorm_mulVec A (P x)).trans_eq (by rw [P.norm_map])

theorem rectangular_reindex_norm (A : Matrix I J ℝ) (e : U≃I) (f : V≃J) :
    ‖A.submatrix e f‖=‖A‖ := by
  refine le_antisymm (rectangular_reindex_le A e f) ?_
  have b := rectangular_reindex_le (A.submatrix e f) e.symm f.symm
  have h : (A.submatrix e f).submatrix e.symm f.symm=A := by
    ext i j
    simp [Matrix.submatrix_apply]
  rwa [h] at b

#print axioms rectangular_reindex_norm
end RobustFolkman.GeometricGap
