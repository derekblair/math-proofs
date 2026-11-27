import GeometricPopulationL2

namespace RobustFolkman.GeometricGap
open MeasureTheory
open scoped ENNReal
variable {S : Type*} [MeasurableSpace S]

/-- Subtracting the expectation is an orthogonal projection in quadratic energy. -/
theorem centered_energy (μ : Measure S) [IsProbabilityMeasure μ]
    (f : S → ℝ) (fm : Measurable f) {B : ℝ} (bd : ∀ x, ‖f x‖ ≤ B) :
    let a := ∫ x, f x ∂μ
    (∫ x, (f x-a) ∂μ)=0 ∧ energyNorm μ (fun x => f x-a) ≤ energyNorm μ f := by
  intro a
  have fi : Integrable f μ := Integrable.of_bound fm.aestronglyMeasurable B (ae_of_all _ bd)
  have B0 : 0 ≤ B := by
    have h := norm_integral_le_of_norm_le_const (μ:=μ) (ae_of_all _ bd)
    exact (norm_nonneg _).trans (by simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h)
  have f2 := bounded_square_integrable f fm B B0 bd μ
  have z : (∫ x, (f x-a) ∂μ)=0 := by
    rw [integral_sub fi (integrable_const _)]
    simp [a]
  refine ⟨z,?_⟩
  unfold energyNorm
  apply Real.sqrt_le_sqrt
  simp_rw [show ∀ x, (f x-a)^2=f x^2-2*a*f x+a^2 by intro x; ring]
  change (∫ x, ((fun z => f z^2) - fun z => (2*a)*f z) x + a^2 ∂μ) ≤ _
  rw [integral_add (f2.sub (fi.const_mul _)) (integrable_const _)]
  simp only [Pi.sub_apply]
  rw [
    integral_sub f2 (fi.const_mul _),integral_const_mul,integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  change (∫ x,f x^2 ∂μ)-2*a*a+a^2≤_
  nlinarith [sq_nonneg a]

#print axioms centered_energy
end RobustFolkman.GeometricGap
