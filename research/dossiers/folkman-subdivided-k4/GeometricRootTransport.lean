import GeometricBandEdges
import GeometricSpanProjection

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem root_shell_isometry (a : UnitSphere E) :
    ∃ (K : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] SphereAmbient (Fin 1) Kᗮ),
      (∀ x : UnitSphere E, sphereHeight (sphereTransport e x)=⟪a.val,x.val⟫_ℝ) ∧
      Module.finrank ℝ E=1+Module.finrank ℝ Kᗮ := by
  classical
  let f : Fin 1 → E := fun _ => a.val
  have fa : ‖a.val‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using a.property
  have o : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    intro i j
    have ij : i=j := Subsingleton.elim _ _
    simp [f,ij,real_inner_self_eq_norm_sq,fa]
  let U : Finset (Fin 1) := Finset.univ
  let K : Submodule ℝ E := Submodule.span ℝ (↑(U.image f) : Set E)
  let b : OrthonormalBasis (Fin 1) ℝ K :=
    (OrthonormalBasis.span o U).reindex (Equiv.subtypeUnivEquiv (fun i => Finset.mem_univ i))
  let e := spanProjectionIsometry K b
  refine ⟨K,e,?_ ,?_⟩
  · intro x
    have bb : ((b 0 : K):E)=a.val := by
      unfold b
      rw [OrthonormalBasis.reindex_apply,OrthonormalBasis.span_apply]
    change (ofLp (ofLp (e x.val)).1) 0 = _
    rw [show e=spanProjectionIsometry K b from rfl,spanProjectionIsometry_coords,bb]
  · rw [e.toLinearEquiv.finrank_eq]
    change Module.finrank ℝ (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Kᗮ))=_
    rw [(WithLp.linearEquiv 2 ℝ (EuclideanSpace ℝ (Fin 1) × Kᗮ)).finrank_eq,
      Module.finrank_prod, finrank_euclideanSpace]
    simp

#print axioms root_shell_isometry
end RobustFolkman.GeometricGap
