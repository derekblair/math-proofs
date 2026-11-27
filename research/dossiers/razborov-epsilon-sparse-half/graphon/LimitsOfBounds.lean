import MarkEnergyLimit

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]

/-- Push a quantitative degree upper bound through varying couplings.
No pointwise subsequence on a fixed sample space is required. -/
theorem aligned_upper_ae (hν : mass ν=1) (g : Y→ℝ) (hg : BMeas g) (b : ℝ)
    (ha : ∀ ε>0, ∃ ρ : Measure (ℝ×Y),
      MeasurePreserving Prod.snd ρ ν ∧
      (∀ᵐ z ∂ρ, z.1≤b+ε) ∧
      Integrable (fun z=>|z.1-g z.2|) ρ ∧
      (∫ z, |z.1-g z.2| ∂ρ)≤ε) :
    ∀ᵐ y ∂ν, g y≤b := by
  let H : Y→ℝ := fun y => max 0 (g y-b)
  have hm : Measurable H := measurable_const.max (hg.1.sub measurable_const)
  have hI : Integrable H ν := by
    obtain ⟨_,C,hC⟩ := hg
    apply integrable_bounded ν (C:=C+|b|) hm (fun _=>le_max_left _ _)
    intro y
    apply max_le
    · linarith [abs_nonneg b,(abs_nonneg (g y)).trans (hC y)]
    · linarith [(le_abs_self (g y)).trans (hC y),neg_abs_le b]
  have hsmall (ε : ℝ) (he : 0<ε) : (∫ y,H y ∂ν)≤2*ε := by
    obtain ⟨ρ,hp,hz,hi,he'⟩ := ha ε he
    have hmap := integral_map (μ:=ρ) hp.measurable.aemeasurable hm.aestronglyMeasurable
    rw [hp.map_eq] at hmap
    have hr : ρ univ = ν univ := by
      rw [← hp.map_eq,Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ]
    haveI : IsFiniteMeasure ρ := ⟨hr ▸ measure_lt_top ν _⟩
    have hM : mass ρ=1 := by
      rw [← hν]
      simp [mass,Measure.real,hr]
    have hIR : Integrable (fun z : ℝ×Y => H z.2) ρ :=
      hp.integrable_comp_of_integrable hI
    have h := integral_mono_ae hIR (hi.add (integrable_const ε)) (by
      filter_upwards [hz] with z hzz
      change max 0 (g z.2-b)≤|z.1-g z.2|+ε
      apply max_le
      · linarith [abs_nonneg (z.1-g z.2)]
      · linarith [neg_abs_le (z.1-g z.2)])
    rw [integral_add' hi (integrable_const ε),integral_const,smul_eq_mul] at h
    change (∫ z, H z.2 ∂ρ)≤(∫ z, |z.1-g z.2| ∂ρ)+mass ρ*ε at h
    rw [← hmap,hM,one_mul] at h
    linarith
  have hzero : (∫ y,H y ∂ν)=0 := by
    have hnn := integral_nonneg (μ:=ν) (f:=H) (fun _=>le_max_left _ _)
    by_contra hne
    have hh := lt_of_le_of_ne hnn (Ne.symm hne)
    have ht := hsmall ((∫ y,H y ∂ν)/3) (by positivity)
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun _=>le_max_left (0:ℝ) _)) hI).mp hzero
  filter_upwards [hae] with y hy
  have hh : g y-b≤H y := le_max_right _ _
  change H y=0 at hy
  linarith

#print axioms aligned_upper_ae
end SparseHalfGraphon
