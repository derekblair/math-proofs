import GeometricRadialIntegration
import GeometricProjectionChange

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal
variable {I : Type*} [Fintype I]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

noncomputable def splitAsProd : Split I ≃ᵐ ((I→ℝ)×ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : I⊕Unit => ℝ)).trans
    ((MeasurableEquiv.refl (I→ℝ)).prodCongr (MeasurableEquiv.funUnique Unit ℝ))

theorem splitAsProd_apply (z : Split I) :
    splitAsProd z=(splitVec z,splitRad z) := rfl

theorem splitAsProd_volume :
    MeasurePreserving (splitAsProd (I:=I)) volume
      ((volume : Measure (I→ℝ)).prod (volume : Measure ℝ)) := by
  unfold splitAsProd
  exact (volume_measurePreserving_sumPiEquivProdPi _).trans <|
    (MeasurePreserving.id _).prod (volume_preserving_funUnique Unit ℝ)

theorem lintegral_splitHalfSpace (f : (I→ℝ)×ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in (splitHalfSpace : Set (Split I)), f (splitVec z,splitRad z)) =
      ∫⁻ u : I→ℝ, ∫⁻ r in Ioi (0:ℝ), f (u,r) := by
  let S : Set ((I→ℝ)×ℝ) := univ ×ˢ Ioi 0
  have hs : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioi
  have ef : splitAsProd ⁻¹' S = (splitHalfSpace : Set (Split I)) := by
    ext z
    simp [splitAsProd_apply, S, splitHalfSpace]
  calc
    _ = ∫⁻ z in (splitAsProd ⁻¹' S), f (splitAsProd z) := by
      simp only [ef,splitAsProd_apply]
    _ = ∫⁻ p in S, f p ∂((volume : Measure (I→ℝ)).prod (volume : Measure ℝ)) :=
      splitAsProd_volume.setLIntegral_comp_preimage hs hf
    _ = _ := by
      rw [← Measure.prod_restrict,Measure.restrict_univ,lintegral_prod _ hf.aemeasurable]

/-- Orthogonal residual directions can be integrated out even when the
weight simultaneously depends on all the projected coordinates. -/
theorem lintegral_residual_split (μ : Measure W) [μ.IsAddHaarMeasure]
    (f : (I→ℝ)×ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f (p.1, ‖p.2‖) ∂((volume : Measure (I→ℝ)).prod μ)) =
      μ.toSphere univ * ∫⁻ z in (splitHalfSpace : Set (Split I)),
        ENNReal.ofReal ((splitRad z)^(Module.finrank ℝ W-1)) * f (splitVec z,splitRad z) := by
  let n := Module.finrank ℝ W-1
  let G : (I→ℝ)×ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (p.2 ^ n)*f p
  have gm : Measurable G := (measurable_snd.pow_const _).ennreal_ofReal.mul hf
  have hm : Measurable (fun p : (I→ℝ)×W => f (p.1, ‖p.2‖)) :=
    hf.comp (measurable_fst.prodMk (measurable_norm.comp measurable_snd))
  rw [lintegral_prod _ hm.aemeasurable]
  have eqn (u : I→ℝ) :
      (∫⁻ w : W, f (u, ‖w‖) ∂μ) =
        μ.toSphere univ * ∫⁻ r in Ioi (0:ℝ), G (u,r) :=
    lintegral_residual_radius μ (fun r => f (u,r)) (hf.comp (measurable_const.prodMk measurable_id))
  simp_rw [eqn]
  rw [lintegral_const_mul' _ _ (measure_ne_top _ _)]
  congr 1
  exact (lintegral_splitHalfSpace G gm).symm

#print axioms lintegral_residual_split
end RobustFolkman.GeometricGap
