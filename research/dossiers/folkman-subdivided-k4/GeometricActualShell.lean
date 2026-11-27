import GeometricExcessChart

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem shellWeight_measurable (t r : ℝ) (r0 : 0≤r) : Measurable (shellWeight t r) := by
  unfold shellWeight
  refine (Real.continuous_rpow_const r0).measurable.comp ?_ |>.ennreal_ofReal
  unfold threeGramDet
  fun_prop

noncomputable def excessTriangleMass (t : ℝ) (S : Set ThreeReals) : ℝ≥0∞ :=
  (Measure.pi (fun _ : Fin 3 => uniformSphere (volume : Measure E)))
    ((chartExcess t ∘ sampleChart) ⁻¹' S)

theorem exact_excess_triangle_measure (m : ℕ) (hm : 0<m) (dim : Module.finrank ℝ E=3+m+1)
    (t : ℝ) (t0 : 0≤t) (t1 : t≤1/4) :
    ∃ K : ℝ≥0∞, ∀ S : Set ThreeReals, MeasurableSet S → S⊆triangleExcessRegion t →
      excessTriangleMass (E:=E) t S = K * (∫⁻ p in S, shellWeight t ((m:ℝ)/2) p) := by
  obtain ⟨C,_,_,law⟩ := spherical_joint_gram_weighted (E:=E) 3 m dim
  let F := chartExcess t
  let A := threeGramDet t t t
  let r := (m:ℝ)/2
  have r0 : 0≤r := by positivity
  have Ap : 0<A := (by norm_num : (0:ℝ)<1/2).trans_le (grain_corner_positive t t0 t1).1
  let R := (ENNReal.ofReal A)^r
  refine ⟨C*R,?_⟩
  intro S sm sub
  have Fm := (chartExcess_volume t).measurable
  let T := F ⁻¹' S
  have Tm : MeasurableSet T := Fm sm
  have H := law (T.indicator (fun _ => 1)) (measurable_const.indicator Tm)
  rw [lintegral_indicator_const_comp sampleChart_measurable Tm 1,one_mul] at H
  change excessTriangleMass (E:=E) t S =
    C * (∫⁻ x, chartWeight 3 m x * T.indicator (fun _ => 1) x) at H
  have cl : (∫⁻ x, chartWeight 3 m x * T.indicator (fun _ => (1:ℝ≥0∞)) x) =
      ∫⁻ x in T, chartWeight 3 m x := by
    rw [←lintegral_indicator Tm]
    apply lintegral_congr
    intro x
    by_cases xx : x∈T <;> simp [indicator_of_mem,indicator_of_notMem,xx]
  have eq : (∫⁻ x in T, chartWeight 3 m x) =
      ∫⁻ x in T, R * shellWeight t r (F x) := by
    apply setLIntegral_congr_fun Tm
    intro x xx
    have h := sub (show F x ∈ S from xx)
    change GramFeasible (fun i j => i≠j) t (excessGram t (F x)) at h
    have hp : (gramChart x).PosSemidef := by
      simpa only [F,chartExcess_gram] using h.1
    let D := threeGramDet (t+(F x).1) (t+(F x).2.1) (t+(F x).2.2)
    have Dd : (gramChart x).det=D := by
      rw [←chartExcess_gram t x,excessGram_det]
    have D0 : 0≤D := Dd ▸ hp.det_nonneg
    rw [chartWeight_psd_power 3 m hm x hp,Dd]
    change ENNReal.ofReal D ^ r = R * ENNReal.ofReal ((D/A)^r)
    nth_rw 1 [show D=A*(D/A) from by field_simp [Ap.ne']]
    rw [ENNReal.ofReal_mul Ap.le, ENNReal.mul_rpow_of_nonneg _ _ r0]
    rw [ENNReal.ofReal_rpow_of_nonneg (div_nonneg D0 Ap.le) r0]
  have fm : Measurable (fun x => shellWeight t r (F x)) :=
    (shellWeight_measurable t r r0).comp Fm
  rw [H,cl,eq,lintegral_const_mul _ fm,←mul_assoc]
  rw [(chartExcess_volume t).setLIntegral_comp_preimage sm (shellWeight_measurable t r r0)]

#print axioms exact_excess_triangle_measure
end RobustFolkman.GeometricGap
