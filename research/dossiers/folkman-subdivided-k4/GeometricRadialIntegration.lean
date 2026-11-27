import GeometricConeRatio

namespace RobustFolkman
open MeasureTheory Set
open scoped ENNReal
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

/-- Integrating out an independent residual direction leaves an exact
Lebesgue power of the radius on the positive half-line. -/
theorem lintegral_residual_radius (μ : Measure W) [μ.IsAddHaarMeasure]
    (f : ℝ→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w : W, f ‖w‖ ∂μ) =
      μ.toSphere (Set.univ) * ∫⁻ r in Set.Ioi (0:ℝ),
        ENNReal.ofReal (r^(Module.finrank ℝ W-1))*f r := by
  let S : Set W := ({0}:Set W)ᶜ
  let F : W→ℝ≥0∞ := fun w => f ‖w‖
  let κ := Measure.volumeIoiPow (Module.finrank ℝ W-1)
  let e := homeomorphUnitSphereProd W
  let g : Metric.sphere (0:W) 1 × Set.Ioi (0:ℝ) → ℝ≥0∞ := fun x => f x.2.val
  have hS : MeasurableSet S := (measurableSet_singleton _).compl
  have full : μ.restrict S = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]
    simp [S])
  have E : (∫⁻ w : W, F w ∂μ) = ∫⁻ v : S, F v.val ∂μ.comap Subtype.val := by
    rw [lintegral_subtype_comap hS F,full]
  have gp : Measurable g := hf.comp (measurable_subtype_coe.comp measurable_snd)
  have law := (μ.measurePreserving_homeomorphUnitSphereProd).lintegral_comp gp
  have eq : (fun x : S => g (e x)) = fun x => F x.val := by
    funext x
    simp [g,e,F,homeomorphUnitSphereProd_apply_snd_coe]
  rw [eq] at law
  change _ = ∫⁻ p, g p ∂μ.toSphere.prod κ at law
  have prod : (∫⁻ p, g p ∂μ.toSphere.prod κ) =
      μ.toSphere Set.univ * ∫⁻ r : Set.Ioi (0:ℝ), f r.val ∂κ := by
    rw [lintegral_prod _ gp.aemeasurable]
    simp [g, lintegral_const, mul_comm]
  rw [E,law,prod]
  congr 1
  have hr : Measurable (fun r : Set.Ioi (0:ℝ) =>
      ENNReal.ofReal (r.val^(Module.finrank ℝ W-1))) :=
    (measurable_subtype_coe.pow_const _).ennreal_ofReal
  unfold κ Measure.volumeIoiPow
  rw [lintegral_withDensity_eq_lintegral_mul _ hr]
  swap
  · exact hf.comp measurable_subtype_coe
  change (∫⁻ r : Set.Ioi (0:ℝ), (fun x : ℝ =>
    ENNReal.ofReal (x^(Module.finrank ℝ W-1))*f x) r.val ∂volume.comap Subtype.val) = _
  exact lintegral_subtype_comap (μ:=volume) (s:=Set.Ioi (0:ℝ)) measurableSet_Ioi
    (fun x : ℝ => ENNReal.ofReal (x^(Module.finrank ℝ W-1))*f x)

#print axioms lintegral_residual_radius
end RobustFolkman
