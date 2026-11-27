import GeometricSphereTransport
import GeometricProjectionLaw
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def spanProjectionIsometry (K : Submodule ℝ E) (b : OrthonormalBasis I ℝ K) :
    E ≃ₗᵢ[ℝ] SphereAmbient I Kᗮ :=
  K.orthogonalDecomposition.trans (b.repr.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ Kᗮ))

theorem spanProjectionIsometry_coords (K : Submodule ℝ E) (b : OrthonormalBasis I ℝ K)
    (x : E) (i : I) :
    (ofLp (ofLp (spanProjectionIsometry K b x)).1) i = ⟪((b i : K) : E),x⟫_ℝ := by
  change b.repr (K.orthogonalDecomposition x).fst i=_
  rw [K.fst_orthogonalDecomposition_apply,b.repr_apply_apply,
    K.inner_orthogonalProjectionOnto_eq_of_mem_left]

theorem sphere_projection_to_span (K : Submodule ℝ E) (b : OrthonormalBasis I ℝ K)
    (m : ℕ) (dim : Module.finrank ℝ Kᗮ = m+2)
    (g : (I→ℝ)→ℝ≥0∞) (gm : Measurable g) :
    (∫⁻ x : UnitSphere E, g (fun i => ⟪((b i : K) : E),x.val⟫_ℝ)
      ∂uniformSphere (volume : Measure E)) =
      (∫⁻ u in (projectionBall : Set (I→ℝ)), projectionFactor m u*g u) /
        (∫⁻ u in (projectionBall : Set (I→ℝ)), projectionFactor m u) := by
  letI : Nontrivial Kᗮ := Module.nontrivial_of_finrank_pos (by rw [dim]; omega)
  let e := spanProjectionIsometry K b
  letI : Nontrivial (SphereAmbient I Kᗮ) := e.injective.nontrivial
  let G : UnitSphere (SphereAmbient I Kᗮ) → ℝ≥0∞ := fun x => g (ofLp (ofLp x.val).1)
  have gp : Measurable G := by
    have eq : G=(g ∘ normalizedCoords ∘ Subtype.val) := by
      funext x
      exact (congrArg g (normalizedCoords_sphere x)).symm
    rw [eq]
    exact gm.comp (normalizedCoords_measurable.comp measurable_subtype_coe)
  have tr := (sphereTransport_volume e).lintegral_comp gp
  have eG (x : UnitSphere E) : G (sphereTransport e x)=g (fun i => ⟪((b i : K) : E),x.val⟫_ℝ) := by
    apply congrArg g
    funext i
    exact spanProjectionIsometry_coords K b x.val i
  simp_rw [eG] at tr
  exact tr.trans (spherical_projection_probability (W:=Kᗮ) m dim g gm)

#print axioms sphere_projection_to_span
end RobustFolkman.GeometricGap
