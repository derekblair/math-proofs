import GeometricGraphMeasure
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace RobustFolkman
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Normalized spherical measure induced by additive Haar measure. -/
noncomputable def uniformSphere (μ : Measure E) : Measure (UnitSphere E) :=
  (μ.toSphere Set.univ)⁻¹ • μ.toSphere

theorem uniformSphere_isProbability (μ : Measure E) [μ.IsAddHaarMeasure] :
    IsProbabilityMeasure (uniformSphere μ) := by
  constructor
  have nz : μ.toSphere Set.univ≠0 := by
    intro h
    exact μ.toSphere_ne_zero (Measure.measure_univ_eq_zero.mp h)
  have nt : μ.toSphere Set.univ≠⊤ := measure_ne_top _ _
  unfold uniformSphere
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.inv_mul_cancel nz nt]

#print axioms uniformSphere_isProbability
end RobustFolkman
