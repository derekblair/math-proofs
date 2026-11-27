import LimitMarkFacts

open Set MeasureTheory Function Filter Topology
namespace SparseHalfGraphon

lemma pospart_sub_bound (x y : ℝ) : |max 0 x - max 0 y| ≤ |x-y| := by
  by_cases hx : 0≤x <;> by_cases hy : 0≤y
  · rw [max_eq_right hx,max_eq_right hy]
  · have hy' := le_of_not_ge hy
    rw [max_eq_right hx,max_eq_left hy',abs_of_nonneg (by linarith),abs_of_nonneg (by linarith : 0≤x-y)]
    linarith
  · have hx' := le_of_not_ge hx
    rw [max_eq_left hx',max_eq_right hy,abs_of_nonpos (by linarith),abs_of_nonpos (by linarith : x-y≤0)]
    linarith
  · simp [max_eq_left (le_of_not_ge hx),max_eq_left (le_of_not_ge hy)]

noncomputable def outsideShortfall {X I : Type*} (c : X→I) (i : I) (g : X→ℝ) (t : ℝ) :=
  (cell c i)ᶜ.indicator (fun x=>max 0 (t-g x))

lemma outsideShortfall_unit {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] (c : X→I) (hc : Measurable c) (i : I)
    (g : X→ℝ) (hg : Measurable g) (hg0 : ∀ x, 0≤g x) (t : ℝ) (ht : t≤1) :
    Measurable (outsideShortfall c i g t) ∧
      ∀ x, 0≤outsideShortfall c i g t x ∧ outsideShortfall c i g t x≤1 := by
  refine ⟨(measurable_const.max (measurable_const.sub hg)).indicator
      (hc (measurableSet_singleton i)).compl,?_⟩
  classical
  intro x
  by_cases hx : x ∈ (cell c i)ᶜ
  · simp only [outsideShortfall,indicator_of_mem hx]
    exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith [hg0 x])⟩
  · simp [outsideShortfall,hx]

theorem aligned_shortfall {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Fintype I]
    (μ : Measure X) (ν : Measure Y) (π : Measure (X×Y))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure π] (hπ : mass π=1)
    (hp : MeasurePreserving Prod.fst π μ) (hq : MeasurePreserving Prod.snd π ν)
    (c : X→I) (d : Y→I) (hc : Measurable c) (hd : Measurable d) (i : I)
    (W : Kernel X) (L : Kernel Y) (ε t : ℝ) (ht : t≤1)
    (hcut : CutBound π (pullKernel W Prod.fst measurable_fst)
      (pullKernel L Prod.snd measurable_snd) ε) :
    (∫ y,outsideShortfall d i (deg (ν.restrict (cell d i)) L) t y ∂ν) ≤
      (∫ x,outsideShortfall c i (deg (μ.restrict (cell c i)) W) t x ∂μ) +
      2*ε + 2*π.real (labelMismatch c d) := by
  let f := deg (μ.restrict (cell c i)) W
  let g := deg (ν.restrict (cell d i)) L
  let a := outsideShortfall c i f t
  let b := outsideShortfall d i g t
  let S := labelMismatch c d
  let s : X×Y→ℝ := S.indicator (fun _=>1)
  have hf := outsideShortfall_unit c hc i f (deg_measurable _ W) (deg_nonneg _ W) t ht
  have hg := outsideShortfall_unit d hd i g (deg_measurable _ L) (deg_nonneg _ L) t ht
  have hS : MeasurableSet S := labelMismatch_meas hc hd
  have hl (z : X×Y) : b z.2 ≤ a z.1+|f z.1-g z.2|+s z := by
    classical
    by_cases hz : z∈S
    · rw [show s z=1 by simp [s,hz]]
      linarith [(hf.2 z.1).1,(hg.2 z.2).2,abs_nonneg (f z.1-g z.2)]
    · have he : c z.1 = d z.2 := not_not.mp hz
      have hs : (z.1∈(cell c i)ᶜ) ↔ (z.2∈(cell d i)ᶜ) := by
        change (¬c z.1=i) ↔ (¬d z.2=i)
        rw [he]
      have h0 : s z=0 := by simp [s,hz]
      rw [h0,add_zero]
      by_cases h : z.1 ∈ (cell c i)ᶜ
      · simp only [a,b,outsideShortfall,indicator_of_mem h,indicator_of_mem (hs.mp h)]
        have h₀ := (abs_le.mp (pospart_sub_bound (t-f z.1) (t-g z.2))).1
        rw [show t-f z.1-(t-g z.2)= -(f z.1-g z.2) by ring,abs_neg] at h₀
        linarith
      · simp [a,b,outsideShortfall,h,mt hs.mpr h]
  have ia : Integrable (fun z:X×Y=>a z.1) π :=
    integrable_bounded π (hf.1.comp measurable_fst) (fun z=> (hf.2 z.1).1) (fun z=> (hf.2 z.1).2)
  have ib : Integrable (fun z:X×Y=>b z.2) π :=
    integrable_bounded π (hg.1.comp measurable_snd) (fun z=> (hg.2 z.2).1) (fun z=> (hg.2 z.2).2)
  have igap : Integrable (fun z:X×Y=>|f z.1-g z.2|) π :=
    (bMeas_integrable π ((bmeas_comp_meas (deg_bmeas _ W) measurable_fst).sub
      (bmeas_comp_meas (deg_bmeas _ L) measurable_snd))).abs
  have iS : Integrable s π := (integrable_const _).indicator hS
  have h := integral_mono ib ((ia.add igap).add iS) hl
  change (∫ z, b z.2 ∂π)≤∫ z,a z.1+|f z.1-g z.2|+s z ∂π at h
  have hs₁ := integral_add' (ia.add igap) iS
  have hs₂ := integral_add' ia igap
  simp only [Pi.add_apply] at hs₁ hs₂
  rw [hs₁,hs₂] at h
  dsimp only [s] at h
  rw [integral_indicator hS,setIntegral_const,smul_eq_mul,mul_one] at h
  have ha := integral_map (μ:=π) hp.measurable.aemeasurable hf.1.aestronglyMeasurable
  have hb := integral_map (μ:=π) hq.measurable.aemeasurable hg.1.aestronglyMeasurable
  rw [hp.map_eq] at ha
  rw [hq.map_eq] at hb
  change (∫ x,a x ∂μ)=(∫ z,a z.1 ∂π) at ha
  change (∫ y,b y ∂ν)=(∫ z,b z.2 ∂π) at hb
  rw [← ha,← hb] at h
  have hdeg := aligned_mark_degree π μ ν hπ hp hq c d hc hd i W L ε hcut
  change (∫ z, |f z.1-g z.2| ∂π)≤_ at hdeg
  exact h.trans (by linarith)

#print axioms aligned_shortfall
end SparseHalfGraphon
