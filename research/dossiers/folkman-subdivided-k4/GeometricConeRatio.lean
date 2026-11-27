import GeometricRotations

namespace RobustFolkman
open MeasureTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The normalized sphere measure is literally a finite unit-ball cone
volume ratio, with no unexplained normalization constant. -/
theorem uniformSphere_cone_ratio (μ : Measure E) [μ.IsAddHaarMeasure]
    (s : Set (UnitSphere E)) (hs : MeasurableSet s) :
    uniformSphere μ s = μ (coneOf s) / μ (Metric.ball 0 1) := by
  have f : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R:=ℝ) (M:=E)).ne'
  have ft : (Module.finrank ℝ E : ℝ≥0∞) ≠ ∞ := by simp
  unfold uniformSphere
  rw [Measure.smul_apply,smul_eq_mul,μ.toSphere_apply_univ,μ.toSphere_apply' hs]
  change ((Module.finrank ℝ E : ℝ≥0∞)*μ (Metric.ball 0 1))⁻¹*
    ((Module.finrank ℝ E : ℝ≥0∞)*μ (coneOf s)) = _
  rw [← ENNReal.div_eq_inv_mul, ENNReal.mul_div_mul_left _ _ f ft]

#print axioms uniformSphere_cone_ratio
end RobustFolkman
