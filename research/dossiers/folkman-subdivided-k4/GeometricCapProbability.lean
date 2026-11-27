import GeometricPairStrip
import GeometricSphericalCompare

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem capPoints_height_interval (t : ℝ) (a : UnitSphere E) :
    capPoints t a=rootHeightStrip a t 1 := by
  ext x
  change t≤⟪a.val,x.val⟫_ℝ ↔ t≤⟪a.val,x.val⟫_ℝ ∧ ⟪a.val,x.val⟫_ℝ≤1
  have z := abs_real_inner_le_norm a.val x.val
  have av : ‖a.val‖=1 := by simpa using a.property
  have xv : ‖x.val‖=1 := by simpa using x.property
  rw [av,xv,mul_one] at z
  exact ⟨fun h => ⟨h,(le_abs_self _).trans z⟩,And.left⟩

theorem cap_threshold_gap_mass (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t s ε : ℝ) (tp : 0<t) (ts : t≤1/8) (r3 : 3≤(n:ℝ)/2)
    (dense : 1≤4*((n:ℝ)/2)*t^2) (s0 : 0≤s) (st : s≤t)
    (small : (4*((n:ℝ)/2)*t*s)*Real.exp (3+4*((n:ℝ)/2)*t*s)≤ε)
    (a : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    σ.real (capPoints (t-s) a \ capPoints t a) ≤ ε*σ.real (capPoints t a) := by
  intro σ
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  have sub : capPoints (t-s) a \ capPoints t a ⊆ rootHeightStrip a (t-s) t := by
    intro x h
    exact ⟨h.1,(lt_of_not_ge h.2).le⟩
  have hm := ENNReal.toReal_mono (measure_ne_top σ _) (measure_mono (μ:=σ) sub)
  have h : σ.real (rootHeightStrip a (t-s) t)≤ε*σ.real (capPoints t a) := by
    change (σ (rootHeightStrip a (t-s) t)).toReal≤ε*(σ (capPoints t a)).toReal
    rw [capPoints_height_interval,root_height_interval n dim a (t-s) t
      (by linarith only [st]) (by linarith only [ts]),
      root_height_interval n dim a t 1 (by linarith only [tp]) le_rfl,
      ENNReal.toReal_div,ENNReal.toReal_div]
    have gap := gap_band_constant ((n:ℝ)/2) t s r3 tp ts dense s0 st
    have upper : sliceMass ((n:ℝ)/2) t 1≠⊤ := ne_of_lt
      ((slice_interval_le_length ((n:ℝ)/2) t 1 (by positivity) (by linarith only [tp]) le_rfl).trans_lt
        ENNReal.ofReal_lt_top)
    have real := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top upper) gap
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at real
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (real.trans (mul_le_mul_of_nonneg_right small ENNReal.toReal_nonneg))
      ENNReal.toReal_nonneg
  exact hm.trans h

#print axioms cap_threshold_gap_mass
end RobustFolkman.GeometricGap
