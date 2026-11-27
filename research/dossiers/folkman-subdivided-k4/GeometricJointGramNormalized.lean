import GeometricJointGram
import GeometricNormalizedRate

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem spherical_joint_gram_normalized (n m : ℕ)
    (dim : Module.finrank ℝ E=n+m+1)
    (f : (PairCoord (Fin n)→ℝ)→ℝ≥0∞) (fm : Measurable f) :
    (∫⁻ v : Fin n→UnitSphere E, f (sampleChart v)
      ∂(Measure.pi fun _ : Fin n => uniformSphere (volume : Measure E))) =
      (∫⁻ x, chartWeight n m x*f x)/(∫⁻ x, chartWeight n m x) := by
  let μ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure μ := uniformSphere_isProbability _
  obtain ⟨C,C0,Ct,law⟩ := spherical_joint_gram_weighted (E:=E) n m dim
  let Z := ∫⁻ x, chartWeight n m x
  have hc := law (fun _ => 1) measurable_const
  simp only [lintegral_const, mul_one,one_mul] at hc
  change (Measure.pi (fun _ : Fin n => μ)) univ = C*Z at hc
  rw [measure_univ] at hc
  have inv : C=Z⁻¹ := by
    have z0 : Z≠0 := by
      intro H
      rw [H,mul_zero] at hc
      exact one_ne_zero hc
    have zt : Z≠∞ := by
      intro H
      rw [H,ENNReal.mul_top C0] at hc
      exact ENNReal.one_ne_top hc
    calc
      C = C * (Z*Z⁻¹) := by rw [ENNReal.mul_inv_cancel z0 zt,mul_one]
      _ = Z⁻¹ := by rw [← mul_assoc,←hc,one_mul]
  rw [law f fm,inv,ENNReal.div_eq_inv_mul]

theorem chartWeight_psd_power (n m : ℕ) (hm : 0<m) (x : PairCoord (Fin n)→ℝ)
    (p : (gramChart x).PosSemidef) :
    chartWeight n m x = (ENNReal.ofReal (gramChart x).det)^((m:ℝ)/2) := by
  by_cases pd : (gramChart x).PosDef
  · rw [chartWeight_at_pd _ _ _ pd,Real.sqrt_eq_rpow,
      ← Real.rpow_mul_natCast pd.det_pos.le,
      show (1/2:ℝ)*m=(m:ℝ)/2 by ring]
    exact (ENNReal.ofReal_rpow_of_nonneg pd.det_pos.le (by positivity)).symm
  · have dz : (gramChart x).det=0 := by
      by_contra dh
      exact pd (pd_of_psd_det _ p dh)
    have xp : x∉chartPD n := pd
    rw [chartWeight,indicator_of_notMem xp,dz,ENNReal.ofReal_zero,ENNReal.zero_rpow_of_pos (by positivity)]

theorem chart_integral_weighted_event (n m : ℕ) (hm : 0<m)
    (C : Fin n→Fin n→Prop) (t : ℝ) :
    (∫⁻ x in chartRegion C t, chartWeight n m x) =
      patternIntegral C t ((m:ℝ)/2) := by
  unfold patternIntegral
  apply setLIntegral_congr_fun (chartRegion_compact C t).measurableSet
  intro x hx
  exact chartWeight_psd_power n m hm x (show GramFeasible C t (gramChart x) from hx).1

#print axioms spherical_joint_gram_normalized
#print axioms chart_integral_weighted_event
end RobustFolkman.GeometricGap
