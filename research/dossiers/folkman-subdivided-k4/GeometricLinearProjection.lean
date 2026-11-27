import GeometricProjectionLaw

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal
variable {I : Type*} [Fintype I]

/-- The conditional projection law can be transported to nonorthogonal
anchor coordinates with a constant inverse determinant Jacobian. -/
theorem linear_projection_pushforward (e : (I→ℝ) ≃L[ℝ] (I→ℝ))
    (s : Set (I→ℝ)) (hs : MeasurableSet s) (f h : (I→ℝ)→ℝ≥0∞) :
    (∫⁻ x in s, f (e x)*h x) =
      ∫⁻ y in e '' s, ENNReal.ofReal |e.symm.toContinuousLinearMap.det| *
        (f y*h (e.symm y)) := by
  let S := e '' s
  have sm : MeasurableSet S := e.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hs
  have ss : e.symm '' S = s := by
    rw [show S = e '' s by rfl, Set.image_image]
    simp
  let g : (I→ℝ) → ℝ≥0∞ := fun x => f (e x)*h x
  have J := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (I→ℝ)) (f:=e.symm)
    (f':=fun _ => e.symm.toContinuousLinearMap) sm
    (fun x _ => e.symm.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)
    e.symm.injective.injOn g
  rw [ss] at J
  refine J.trans ?_
  simp [g,S]

#print axioms linear_projection_pushforward
end RobustFolkman.GeometricGap
