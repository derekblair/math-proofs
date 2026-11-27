import LimitDegreeCap

open Set MeasureTheory Function Filter Topology
open scoped ENNReal
namespace SparseHalfGraphon

/-- Limit marks retain their masses and any zero internal edge mass. -/
theorem cut_limit_mark_facts {Z : ℕ→Type*} [∀ k, MeasurableSpace (Z k)]
    {Y I : Type*} [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSingletonClass I] [Fintype I]
    (μ : ∀ k, Measure (Z k)) [∀ k, IsFiniteMeasure (μ k)] (ν : Measure Y) [IsFiniteMeasure ν]
    (W : ∀ k, Kernel (Z k)) (L : Kernel Y)
    (c : ∀ k, Z k→I) (d : Y→I) (hc : ∀ k, Measurable (c k)) (hd : Measurable d) (i : I)
    (b : ℝ) (hB : Tendsto (fun k => (μ k).real (cell (c k) i)) atTop (𝓝 b))
    (hInd : ∀ k, energyPair (μ k) (W k) (markWeight (c k) i) (markWeight (c k) i)=0)
    (ha : ∀ ε>0, ∀ᶠ k in atTop, ∃ π : Measure (Z k×Y),
      MeasurePreserving Prod.fst π (μ k) ∧ MeasurePreserving Prod.snd π ν ∧
      π univ = 1 ∧ π.real (labelMismatch (c k) d)≤ε ∧
      CutBound π (pullKernel (W k) Prod.fst measurable_fst)
        (pullKernel L Prod.snd measurable_snd) ε) :
    ν.real (cell d i)=b ∧ energyPair ν L (markWeight d i) (markWeight d i)=0 := by
  have H (ε : ℝ) (he : 0<ε) : |ν.real (cell d i)-b|≤2*ε ∧
      |energyPair ν L (markWeight d i) (markWeight d i)|≤4*ε := by
    obtain ⟨k,⟨π,hp,hq,hπ,hm,hcut⟩,ht⟩ :=
      ((ha ε he).and (Metric.tendsto_nhds.mp hB ε he)).exists
    have : IsFiniteMeasure π := ⟨by rw [hπ]; exact ENNReal.one_lt_top⟩
    have hp' : mass π=1 := by simp [mass,Measure.real,hπ]
    have h1 := aligned_mark_mass π (μ k) ν hp hq (c k) d (hc k) hd i
    have h2 := aligned_mark_energy (μ k) ν π hp' hp hq (c k) d (hc k) hd i (W k) L ε hcut
    rw [hInd k,zero_sub,abs_neg] at h2
    rw [Real.dist_eq] at ht
    exact ⟨(abs_sub_le _ ((μ k).real (cell (c k) i)) _).trans (by
        rw [abs_sub_comm (ν.real (cell d i))]
        linarith only [h1,hm,ht]),
      h2.trans (by linarith only [hm])⟩
  constructor
  · by_contra hn
    have hp : 0 < |ν.real (cell d i)-b| := abs_pos.mpr (sub_ne_zero.mpr hn)
    have h := (H (|ν.real (cell d i)-b|/3) (by positivity)).1
    linarith
  · by_contra hn
    have hp : 0 < |energyPair ν L (markWeight d i) (markWeight d i)| := abs_pos.mpr hn
    have h := (H (|energyPair ν L (markWeight d i) (markWeight d i)|/5) (by positivity)).2
    linarith

#print axioms cut_limit_mark_facts
end SparseHalfGraphon
