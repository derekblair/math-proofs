import GeometricResidualSplit

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal
variable {I : Type*} [Fintype I]

def projectionBall : Set (I→ℝ) := {x | ∑ i, x i ^ 2 < 1}
noncomputable def projectionFactor (m : ℕ) (x : I→ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (1-∑ i, x i ^ 2))^m)

theorem projectionBall_measurable : MeasurableSet (projectionBall : Set (I→ℝ)) := by
  have h (i : I) : Continuous (fun x : I→ℝ => x i ^ 2) := (continuous_apply i).pow 2
  exact (isOpen_lt (continuous_finsetSum _ fun i _ => h i) continuous_const).measurableSet

theorem projectionFactor_measurable (m : ℕ) : Measurable (projectionFactor (I:=I) m) := by
  exact (((measurable_const.sub (Finset.measurable_fun_sum _ fun i _ =>
    (measurable_pi_apply i).pow_const 2)).sqrt).pow_const _).ennreal_ofReal

theorem splitPolarDomain_prod :
    splitAsProd ⁻¹' ((projectionBall : Set (I→ℝ)) ×ˢ Ioi (0:ℝ)) =
      (splitPolarDomain : Set (Split I)) := by
  ext z
  simp only [Set.mem_preimage,splitAsProd_apply,Set.mem_prod,projectionBall,Set.mem_setOf_eq,
    splitPolarDomain, Set.mem_Ioi, splitRest, sub_pos]

theorem projection_factor_fubini (m : ℕ) (g : (I→ℝ)→ℝ≥0∞) (h : ℝ→ℝ≥0∞)
    (gm : Measurable g) (hm : Measurable h) :
    (∫⁻ z in (splitPolarDomain : Set (Split I)),
      (projectionFactor m (splitVec z)*g (splitVec z)) *
      (ENNReal.ofReal ((splitRad z)^(Fintype.card I+m+1))*h (splitRad z))) =
    (∫⁻ x in (projectionBall : Set (I→ℝ)), projectionFactor m x*g x) *
      (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Fintype.card I+m+1))*h r) := by
  let f : (I→ℝ)→ℝ≥0∞ := fun x => projectionFactor m x*g x
  let q : ℝ→ℝ≥0∞ := fun r => ENNReal.ofReal (r^(Fintype.card I+m+1))*h r
  have fm : Measurable f := (projectionFactor_measurable m).mul gm
  have qm : Measurable q := (measurable_id.pow_const _).ennreal_ofReal.mul hm
  change (∫⁻ z in (splitPolarDomain : Set (Split I)), f (splitVec z)*q (splitRad z)) = _
  rw [← splitPolarDomain_prod]
  let F : ((I→ℝ)×ℝ)→ℝ≥0∞ := fun p => f p.1*q p.2
  have fm2 : Measurable F := (fm.comp measurable_fst).mul (qm.comp measurable_snd)
  change (∫⁻ z in splitAsProd ⁻¹' _, F (splitAsProd z)) = _
  rw [splitAsProd_volume.setLIntegral_comp_preimage
    (projectionBall_measurable.prod (measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ)))) fm2]
  rw [← Measure.prod_restrict]
  exact lintegral_prod_mul fm.aemeasurable qm.aemeasurable

#print axioms projection_factor_fubini
end RobustFolkman.GeometricGap
