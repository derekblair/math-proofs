import GeometricSpanAnchors
import GeometricGramTelescope

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp Matrix
open scoped ENNReal InnerProductSpace
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def anchorGram (v : I→E) : Matrix I I ℝ := fun i j => ⟪v i,v j⟫_ℝ
noncomputable def anchorQuad (A : Matrix I I ℝ) (y : I→ℝ) := y ⬝ᵥ (A⁻¹ *ᵥ y)

theorem sphere_anchor_conditional (K : Submodule ℝ E) (b : OrthonormalBasis I ℝ K)
    (v : I→K) (ind : LinearIndependent ℝ v)
    (m : ℕ) (dim : Module.finrank ℝ Kᗮ = m+2) (g : (I→ℝ)→ℝ≥0∞) (gm : Measurable g) :
    let A := anchorGram (fun i => (v i:E))
    (∫⁻ x : UnitSphere E, g (fun i => ⟪(v i:E),x.val⟫_ℝ) ∂uniformSphere (volume : Measure E)) =
      (∫⁻ y in {y | anchorQuad A y<1},
        ENNReal.ofReal ((Real.sqrt A.det)⁻¹) *
          (g y*ENNReal.ofReal ((Real.sqrt (1-anchorQuad A y))^m))) /
        (∫⁻ u in (projectionBall : Set (I→ℝ)), projectionFactor m u) := by
  intro A
  let T := spanAnchorMatrix K b v
  have un : IsUnit T.det := spanAnchorMatrix_isUnit K b v ind
  have de : IsUnit (Matrix.toLin' T).det := by rwa [LinearMap.det_toLin']
  let e := (LinearMap.equivOfIsUnitDet de).toContinuousLinearEquiv
  have ev (x : I→ℝ) : e x = T*ᵥx := by
    change ((LinearMap.equivOfIsUnitDet de : (I→ℝ) ≃ₗ[ℝ] (I→ℝ)) : (I→ℝ) →ₗ[ℝ] (I→ℝ)) x=T*ᵥx
    rw [LinearMap.coe_equivOfIsUnitDet,Matrix.toLin'_apply]
  have gt : Measurable (fun u => g (e u)) := gm.comp e.continuous.measurable
  have law := sphere_projection_to_span K b m dim (fun u => g (e u)) gt
  have apps (x : UnitSphere E) :
      e (fun i => ⟪((b i : K) : E),x.val⟫_ℝ) = fun i => ⟪(v i:E),x.val⟫_ℝ :=
    (ev _).trans (spanAnchorMatrix_apply K b v x.val)
  simp_rw [apps] at law
  rw [law]
  have eq : A=T*T.transpose := (spanAnchorMatrix_gram K b v).symm
  rw [eq]
  congr 1
  have com : (fun u => projectionFactor m u * g (e u)) =
      fun u => g (e u) * projectionFactor m u := by
    funext u
    rw [mul_comm]
  rw [com, anchor_density_integral e T un ev m g, anchor_inverse_jacobian e T ev]
  rfl

#print axioms sphere_anchor_conditional
end RobustFolkman.GeometricGap
