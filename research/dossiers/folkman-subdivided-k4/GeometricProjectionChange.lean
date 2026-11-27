import GeometricProjectionInverse
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set
open scoped ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem splitPolarDomain_open : IsOpen (splitPolarDomain : Set (Split I)) := by
  have hc (i : I) : Continuous (fun z : Split I => splitVec z i ^ 2) :=
    (continuous_apply (Sum.inl i : I ⊕ Unit)).pow 2
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (continuous_const.sub (continuous_finsetSum _ fun i _ => hc i))
  · exact isOpen_lt continuous_const (continuous_apply (Sum.inr () : I ⊕ Unit))

theorem splitPolar_lintegral (g : Split I → ℝ≥0∞) :
    (∫⁻ w in (splitHalfSpace : Set (Split I)), g w) =
    ∫⁻ z in (splitPolarDomain : Set (Split I)),
      ENNReal.ofReal ((splitRad z)^(Fintype.card I)/Real.sqrt (splitRest z)) * g (splitPolar z) := by
  rw [← splitPolar_image_domain]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume splitPolarDomain_open.measurableSet
    (fun z hz => (splitPolar_derivative z hz.1).hasFDerivWithinAt) splitPolar_injOn g]
  apply setLIntegral_congr_fun splitPolarDomain_open.measurableSet
  intro z hz
  change 0 < splitRest z ∧ 0 < splitRad z at hz
  dsimp only
  rw [splitPolar_derivative_det z hz.1, abs_of_nonneg (div_nonneg (pow_nonneg hz.2.le _) (Real.sqrt_nonneg _))]

/-- The dimension-dependent radial power separates exactly from the
projection factor after the split-polar change of variables. -/
theorem splitPolar_weight (z : Split I) (hz : z∈splitPolarDomain) (m : ℕ) :
    ((splitRad z)^(Fintype.card I)/Real.sqrt (splitRest z)) *
      (splitRad (splitPolar z))^(m+1) =
    (splitRad z)^(Fintype.card I+m+1)*(Real.sqrt (splitRest z))^m := by
  simp only [splitPolar_rad,mul_pow,pow_add,pow_one]
  have s0 := (Real.sqrt_pos.2 hz.1).ne'
  field_simp
  <;> ring

/-- Split the weighted cone integral into its projected coordinates
and a single radial variable. The Haar/sphere connection is separate. -/
theorem splitPolar_weighted_lintegral (wgt : (I→ℝ) → ℝ≥0∞) (radial : ℝ → ℝ≥0∞) (m : ℕ) :
    (∫⁻ w in (splitHalfSpace : Set (Split I)),
      ENNReal.ofReal ((splitRad w)^(m+1)) *
        (wgt (splitVec (splitPolarInv w)) * radial (splitRadius w))) =
    ∫⁻ z in (splitPolarDomain : Set (Split I)),
      ENNReal.ofReal ((splitRad z)^(Fintype.card I+m+1) *
        (Real.sqrt (splitRest z))^m) * (wgt (splitVec z) * radial (splitRad z)) := by
  rw [splitPolar_lintegral]
  apply setLIntegral_congr_fun splitPolarDomain_open.measurableSet
  intro z hz
  dsimp only
  rw [splitPolar_left_inverse hz,splitRadius_polar z hz.1.le hz.2.le,
    ← mul_assoc,← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hz.2.le _) (Real.sqrt_nonneg _)),
    splitPolar_weight z hz m]

#print axioms splitPolar_weighted_lintegral
#print axioms splitPolar_lintegral
#print axioms splitPolar_weight
end RobustFolkman.GeometricGap
