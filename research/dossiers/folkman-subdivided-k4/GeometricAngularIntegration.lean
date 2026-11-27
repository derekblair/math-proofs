import GeometricRadialIntegration

namespace RobustFolkman
open MeasureTheory Set
open scoped ENNReal
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

/-- Radial-angular product formula for any measurable scale-invariant
weight, not only constant weights on directions. -/
theorem lintegral_angular_radial (μ : Measure W) [μ.IsAddHaarMeasure]
    (g : W→ℝ≥0∞) (gm : Measurable g)
    (invar : ∀ (w : W) (a : ℝ), 0<a → g (a • w)=g w)
    (h : ℝ→ℝ≥0∞) (hm : Measurable h) :
    (∫⁻ w : W, g w*h ‖w‖ ∂μ) =
      (∫⁻ u : Metric.sphere (0:W) 1, g u.val ∂μ.toSphere) *
      ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Module.finrank ℝ W-1))*h r := by
  let S : Set W := ({0}:Set W)ᶜ
  let F : W→ℝ≥0∞ := fun w => g w*h ‖w‖
  let κ := Measure.volumeIoiPow (Module.finrank ℝ W-1)
  let e := homeomorphUnitSphereProd W
  let G : Metric.sphere (0:W) 1×Set.Ioi (0:ℝ) → ℝ≥0∞ :=
    fun p => g p.1.val*h p.2.val
  have hS : MeasurableSet S := (measurableSet_singleton _).compl
  have full : μ.restrict S = μ := Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; simp [S])
  have E : (∫⁻ w : W, F w ∂μ) = ∫⁻ v : S, F v.val ∂μ.comap Subtype.val := by
    rw [lintegral_subtype_comap hS F,full]
  have Gm : Measurable G := (gm.comp (measurable_subtype_coe.comp measurable_fst)).mul
    (hm.comp (measurable_subtype_coe.comp measurable_snd))
  have law := (μ.measurePreserving_homeomorphUnitSphereProd).lintegral_comp Gm
  have eq : (fun x : S => G (e x)) = fun x => F x.val := by
    funext x
    have x0 : x.val ≠ 0 := x.property
    have hp : 0 < ‖x.val‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr x0)
    simp [G,e,F,homeomorphUnitSphereProd_apply_snd_coe,homeomorphUnitSphereProd_apply_fst_coe,
      invar _ _ hp]
  rw [eq] at law
  change _ = ∫⁻ p, G p ∂μ.toSphere.prod κ at law
  rw [E,law]
  unfold G
  rw [lintegral_prod_mul (μ:=μ.toSphere) (ν:=κ)
    (f:=fun u : Metric.sphere (0:W) 1 => g u.val)
    (g:=fun t : Set.Ioi (0:ℝ) => h t.val)
    (gm.comp measurable_subtype_coe).aemeasurable
    (hm.comp measurable_subtype_coe).aemeasurable]
  congr 1
  have hr : Measurable (fun r : Set.Ioi (0:ℝ) =>
      ENNReal.ofReal (r.val^(Module.finrank ℝ W-1))) :=
    (measurable_subtype_coe.pow_const _).ennreal_ofReal
  unfold κ Measure.volumeIoiPow
  rw [lintegral_withDensity_eq_lintegral_mul _ hr (show Measurable (fun r : Set.Ioi (0:ℝ) => h r.val) from hm.comp measurable_subtype_coe)]
  exact lintegral_subtype_comap (μ:=volume) (s:=Set.Ioi (0:ℝ)) measurableSet_Ioi
    (fun x : ℝ => ENNReal.ofReal (x^(Module.finrank ℝ W-1))*h x)

#print axioms lintegral_angular_radial
end RobustFolkman
