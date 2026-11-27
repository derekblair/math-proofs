import GeometricProjectionFubini

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

noncomputable def pairRadius (p : (I→ℝ)×ℝ) : ℝ := Real.sqrt ((∑ i, p.1 i^2)+p.2^2)
noncomputable def pairProjection (p : (I→ℝ)×ℝ) : I→ℝ := fun i => p.1 i/pairRadius p

theorem pairRadius_measurable : Measurable (pairRadius (I:=I)) :=
  ((Finset.measurable_fun_sum _ fun i _ => ((measurable_pi_apply i).comp measurable_fst).pow_const 2).add
    (measurable_snd.pow_const 2)).sqrt

theorem pairProjection_measurable : Measurable (pairProjection (I:=I)) := by
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i).comp measurable_fst).div pairRadius_measurable

/-- Full separation of the projection, residual directions, and overall
radius in Lebesgue measure on an orthogonally split vector space. -/
theorem lintegral_product_projection (μ : Measure W) [μ.IsAddHaarMeasure] (m : ℕ)
    (dim : Module.finrank ℝ W=m+2)
    (g : (I→ℝ)→ℝ≥0∞) (gm : Measurable g) (h : ℝ→ℝ≥0∞) (hm : Measurable h) :
    (∫⁻ p, g (pairProjection (p.1, ‖p.2‖))*h (pairRadius (p.1,‖p.2‖))
      ∂((volume : Measure (I→ℝ)).prod μ)) =
      μ.toSphere univ *
       ((∫⁻ x in (projectionBall : Set (I→ℝ)), projectionFactor m x*g x) *
        (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Fintype.card I+m+1))*h r)) := by
  let f : ((I→ℝ)×ℝ)→ℝ≥0∞ := fun p => g (pairProjection p)*h (pairRadius p)
  have fm : Measurable f := (gm.comp pairProjection_measurable).mul (hm.comp pairRadius_measurable)
  have eq : Module.finrank ℝ W-1=m+1 := by omega
  change (∫⁻ p, f (p.1, ‖p.2‖) ∂((volume : Measure (I→ℝ)).prod μ)) = _
  rw [lintegral_residual_split μ f fm,eq]
  congr 1
  unfold f
  change (∫⁻ z in (splitHalfSpace : Set (Split I)),
    ENNReal.ofReal (splitRad z^(m+1))*(g (splitVec (splitPolarInv z))*h (splitRadius z))) = _
  rw [splitPolar_weighted_lintegral g h m,← projection_factor_fubini m g h gm hm]
  apply setLIntegral_congr_fun splitPolarDomain_open.measurableSet
  intro z hz
  dsimp only
  have nr : 0≤(splitRad z)^(Fintype.card I+m+1) := pow_nonneg hz.2.le _
  rw [ENNReal.ofReal_mul nr]
  unfold projectionFactor splitRest
  ac_rfl

#print axioms lintegral_product_projection
end RobustFolkman.GeometricGap
