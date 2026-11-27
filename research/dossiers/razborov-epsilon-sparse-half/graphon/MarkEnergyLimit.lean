import MarkedLimits

open Set MeasureTheory Function
open scoped symmDiff
namespace SparseHalfGraphon

lemma bmeas_comp_meas {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : Y→ℝ} (hf : BMeas f) {g : X→Y} (hg : Measurable g) : BMeas (f ∘ g) := by
  obtain ⟨hm,C,hC⟩ := hf
  exact ⟨hm.comp hg,C,fun x=>hC (g x)⟩

noncomputable def markWeight {X I : Type*} (c : X→I) (i : I) : X→ℝ :=
  (cell c i).indicator (fun _=>1)

lemma markWeight_meas {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] {c : X→I} (hc : Measurable c) (i : I) :
    Measurable (markWeight c i) :=
  measurable_const.indicator (hc (measurableSet_singleton i))

lemma markWeight_nonneg {X I : Type*} (c : X→I) (i : I) (x : X) :
    0≤markWeight c i x := by
  classical
  by_cases h : x∈cell c i <;> simp [markWeight,h]

lemma markWeight_le_one {X I : Type*} (c : X→I) (i : I) (x : X) :
    markWeight c i x≤1 := by
  classical
  by_cases h : x∈cell c i <;> simp [markWeight,h]

lemma markEnergy_rows {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] (μ : Measure X) [IsFiniteMeasure μ]
    (W : Kernel X) (c : X→I) (hc : Measurable c) (i : I) :
    energyPair μ W (markWeight c i) (markWeight c i) =
      ∫ x, markWeight c i x * deg (μ.restrict (cell c i)) W x ∂μ := by
  have b := BMeas.of_unit (markWeight_meas hc i) (markWeight_nonneg c i) (markWeight_le_one c i)
  rw [energy_row μ W _ _ b b]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change markWeight c i x * weightedDegree μ W (markWeight c i) x =
    markWeight c i x * deg (μ.restrict (cell c i)) W x
  congr 1
  unfold weightedDegree deg
  have he : MeasurableSet (cell c i) := hc (measurableSet_singleton i)
  rw [← integral_indicator he]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  classical
  by_cases h : y∈cell c i
  · simpa [markWeight,h] using W.symm y x
  · simp [markWeight,h]

variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I]
  [MeasurableSingletonClass I] [Fintype I]

/-- The marked internal edge mass is preserved along jointly aligned
kernels and finite labels, with explicit cut and mark error. -/
theorem aligned_mark_energy (μ : Measure X) (ν : Measure Y) (π : Measure (X×Y))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure π] (hπ : mass π=1)
    (hp : MeasurePreserving Prod.fst π μ) (hq : MeasurePreserving Prod.snd π ν)
    (c : X→I) (d : Y→I) (hc : Measurable c) (hd : Measurable d) (i : I)
    (W : Kernel X) (L : Kernel Y) (ε : ℝ)
    (hcut : CutBound π (pullKernel W Prod.fst measurable_fst) (pullKernel L Prod.snd measurable_snd) ε) :
    |energyPair μ W (markWeight c i) (markWeight c i) -
      energyPair ν L (markWeight d i) (markWeight d i)| ≤
      2*ε + 2*π.real (labelMismatch c d) := by
  let a : X×Y → ℝ := (markWeight c i) ∘ Prod.fst
  let b : X×Y → ℝ := (markWeight d i) ∘ Prod.snd
  let U : X×Y → ℝ := (deg (μ.restrict (cell c i)) W) ∘ Prod.fst
  let V : X×Y → ℝ := (deg (ν.restrict (cell d i)) L) ∘ Prod.snd
  let S := labelMismatch c d
  let s : X×Y → ℝ := S.indicator (fun _=>1)
  have hS : MeasurableSet S := labelMismatch_meas hc hd
  have a0 (x) : 0≤a x := markWeight_nonneg c i x.1
  have a1 (x) : a x≤1 := markWeight_le_one c i x.1
  have b0 (x) : 0≤b x := markWeight_nonneg d i x.2
  have b1 (x) : b x≤1 := markWeight_le_one d i x.2
  have hν : mass ν=1 := by rw [← hq.map_eq,map_mass Prod.snd measurable_snd,hπ]
  have v0 (x) : 0≤V x := deg_nonneg (ν.restrict (cell d i)) L x.2
  have v1 (x) : V x≤1 := by
    change deg (ν.restrict (cell d i)) L x.2 ≤ _
    refine (deg_le_mass _ L x.2).trans ?_
    unfold mass at *
    rw [← hν]
    rw [measureReal_restrict_apply_univ]
    exact measureReal_mono (subset_univ _)
  classical
  have hdiff (x) : |a x-b x|≤s x := by
    by_cases hm : x∈S
    · rw [show s x=1 by simp [s,hm],abs_le]
      constructor <;> linarith [a0 x,a1 x,b0 x,b1 x]
    · have hh : c x.1=d x.2 := not_not.mp hm
      change |markWeight c i x.1 - markWeight d i x.2|≤s x
      have ht : x.1∈cell c i ↔ x.2∈cell d i := by change (c x.1=i) ↔ (d x.2=i); rw [hh]
      by_cases hx : x.1 ∈ cell c i
      · simp [markWeight,hx,ht.mp hx,s,hm]
      · simp [markWeight,hx,mt ht.mpr hx,s,hm]
  have hpoint (x) : |a x*U x-b x*V x|≤|U x-V x|+s x := by
    rw [show a x*U x-b x*V x=a x*(U x-V x)+(a x-b x)*V x by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (a0 x),abs_of_nonneg (v0 x)]
    exact add_le_add ((mul_le_mul_of_nonneg_right (a1 x) (abs_nonneg _)).trans_eq (one_mul _))
      (((mul_le_mul_of_nonneg_left (v1 x) (abs_nonneg _)).trans_eq (mul_one _)).trans (hdiff x))
  rw [markEnergy_rows μ W c hc i,markEnergy_rows ν L d hd i]
  have ia : Integrable (fun x => a x*U x) π := bMeas_integrable π ((BMeas.of_unit ((markWeight_meas hc i).comp measurable_fst) a0 a1).mul
    (bmeas_comp_meas (deg_bmeas (μ.restrict (cell c i)) W) measurable_fst))
  have ib : Integrable (fun x => b x*V x) π := bMeas_integrable π ((BMeas.of_unit ((markWeight_meas hd i).comp measurable_snd) b0 b1).mul
    (bmeas_comp_meas (deg_bmeas (ν.restrict (cell d i)) L) measurable_snd))
  have iUV : Integrable (fun x => |U x-V x|) π := (bMeas_integrable π ((bmeas_comp_meas (deg_bmeas (μ.restrict (cell c i)) W) measurable_fst).sub
    (bmeas_comp_meas (deg_bmeas (ν.restrict (cell d i)) L) measurable_snd))).abs
  have is : Integrable s π := (integrable_const _).indicator hS
  have hx := integral_mono (ia.sub ib).abs (iUV.add is) hpoint
  change (∫ x, |a x*U x-b x*V x| ∂π)≤∫ x, |U x-V x|+s x ∂π at hx
  rw [integral_add iUV is] at hx
  dsimp only [s] at hx
  rw [integral_indicator hS,setIntegral_const,smul_eq_mul,mul_one] at hx
  have hpa := integral_map (μ:=π) hp.measurable.aemeasurable
    ((markWeight_meas hc i).mul (deg_measurable (μ.restrict (cell c i)) W)).aestronglyMeasurable
  have hqa := integral_map (μ:=π) hq.measurable.aemeasurable
    ((markWeight_meas hd i).mul (deg_measurable (ν.restrict (cell d i)) L)).aestronglyMeasurable
  rw [hp.map_eq] at hpa
  rw [hq.map_eq] at hqa
  simp only [Pi.mul_apply] at hpa hqa
  rw [hpa,hqa]
  change |(∫ x, a x*U x ∂π)-(∫ x, b x*V x ∂π)|≤_
  have hnorm := norm_integral_le_integral_norm (μ:=π) (f:=fun x=>a x*U x-b x*V x)
  rw [integral_sub ia ib] at hnorm
  simp only [Real.norm_eq_abs] at hnorm
  have hD := aligned_mark_degree π μ ν hπ hp hq c d hc hd i W L ε hcut
  change (∫ x, |U x-V x| ∂π) ≤ _ at hD
  change _ ≤ (∫ x, |U x-V x| ∂π)+π.real S at hx
  linarith [hnorm,hx,hD]

#print axioms aligned_mark_energy
end SparseHalfGraphon
