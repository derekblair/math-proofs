import GeometricSharedRoot
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace RobustFolkman
open MeasureTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Uniform upper Laplace bound for the determinant powers on a
measurable region. The Gram density theorem is a separate input. -/
theorem upper_power_integral (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s)
    (g : Ω→ℝ≥0∞) (M : ℝ≥0∞) (p : ℝ) (hp : 0≤p)
    (upper : ∀ x∈s, g x≤M) :
    (∫⁻ x in s, (g x)^p ∂μ)≤M^p*μ s := by
  calc
    _ ≤ ∫⁻ _ in s, M^p ∂μ := setLIntegral_mono' hs fun x hx =>
      ENNReal.rpow_le_rpow (upper x hx) hp
    _ = _ := by rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

/-- Lower Laplace bound from any measurable neighborhood where the
determinant stays above a chosen level. -/
theorem lower_power_integral (μ : Measure Ω) {r s : Set Ω}
    (hr : MeasurableSet r) (sub : r⊆s) (g : Ω→ℝ≥0∞) (m : ℝ≥0∞) (p : ℝ) (hp : 0≤p)
    (lower : ∀ x∈r, m≤g x) :
    m^p*μ r≤ ∫⁻ x in s, (g x)^p ∂μ := by
  calc
    _ = ∫⁻ _ in r, m^p ∂μ := by rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    _ ≤ ∫⁻ x in r, (g x)^p ∂μ := setLIntegral_mono' hr fun x hx =>
      ENNReal.rpow_le_rpow (lower x hx) hp
    _ ≤ _ := lintegral_mono' (Measure.restrict_mono_set μ sub) le_rfl

#print axioms upper_power_integral
#print axioms lower_power_integral
end RobustFolkman
