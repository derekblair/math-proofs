import LowerMarked

open Set MeasureTheory Function Filter Topology
open scoped ENNReal
namespace SparseHalfGraphon

/-- Vanishing average shortfall in the samples gives the marked
minimum degree outside the limit mark, almost everywhere. -/
theorem cut_limit_outside_floor {Z : ℕ→Type*} [∀ k, MeasurableSpace (Z k)]
    {Y I : Type*} [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSingletonClass I] [Fintype I]
    (μ : ∀ k, Measure (Z k)) [∀ k, IsFiniteMeasure (μ k)] (ν : Measure Y) [IsFiniteMeasure ν]
    (W : ∀ k, Kernel (Z k)) (L : Kernel Y)
    (c : ∀ k, Z k→I) (d : Y→I) (hc : ∀ k, Measurable (c k)) (hd : Measurable d) (i : I)
    (t : ℝ) (ht : t≤1)
    (hB : Tendsto (fun k => ∫ x, outsideShortfall (c k) i
      (deg ((μ k).restrict (cell (c k) i)) (W k)) t x ∂μ k) atTop (𝓝 0))
    (ha : ∀ ε > 0, ∀ᶠ k in atTop, ∃ π : Measure (Z k × Y),
      MeasurePreserving Prod.fst π (μ k) ∧ MeasurePreserving Prod.snd π ν ∧
      π univ = 1 ∧ π.real (labelMismatch (c k) d)≤ε ∧
      CutBound π (pullKernel (W k) Prod.fst measurable_fst)
        (pullKernel L Prod.snd measurable_snd) ε) :
    ∀ᵐ y ∂ν, y ∉ cell d i → t ≤ deg (ν.restrict (cell d i)) L y := by
  let g := deg (ν.restrict (cell d i)) L
  let f := outsideShortfall d i g t
  have hb := outsideShortfall_unit d hd i g (deg_measurable _ L) (deg_nonneg _ L) t ht
  have fI : Integrable f ν := integrable_bounded _ hb.1 (fun x=>(hb.2 x).1) (fun x=>(hb.2 x).2)
  have hi (ε : ℝ) (he : 0<ε) : (∫ x,f x ∂ν)≤5*ε := by
    obtain ⟨k,⟨π,hp,hq,hπ,hm,hcut⟩,hb'⟩ :=
      ((ha ε he).and (Metric.tendsto_nhds.mp hB ε he)).exists
    have : IsFiniteMeasure π := ⟨by rw [hπ]; exact ENNReal.one_lt_top⟩
    have hp' : mass π=1 := by simp [mass,Measure.real,hπ]
    have h := aligned_shortfall (μ k) ν π hp' hp hq (c k) d (hc k) hd i (W k) L ε t ht hcut
    rw [Real.dist_eq,sub_zero] at hb'
    have hf := (le_abs_self _).trans hb'.le
    change (∫ y,f y ∂ν)≤_ at h
    linarith only [h,hf,hm]
  have hz : (∫ x,f x ∂ν)=0 := by
    have h0 := integral_nonneg (μ:=ν) (f:=f) (fun x=>(hb.2 x).1)
    by_contra hn
    have hpos := lt_of_le_of_ne h0 (Ne.symm hn)
    have hh := hi ((∫ x,f x ∂ν)/6) (by positivity)
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun x=>(hb.2 x).1)) fI).mp hz
  filter_upwards [hae] with y hy hny
  change f y=0 at hy
  have hh : max 0 (t-g y)=0 := by
    simpa only [f,outsideShortfall,indicator_of_mem (mem_compl hny)] using hy
  have hle : t-g y≤0 := (le_max_right (0:ℝ) _).trans_eq hh
  linarith

#print axioms cut_limit_outside_floor
end SparseHalfGraphon
