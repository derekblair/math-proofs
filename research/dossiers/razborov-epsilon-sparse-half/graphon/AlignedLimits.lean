import TowerCompactness

open Set MeasureTheory Function Filter Topology
open scoped ENNReal
namespace SparseHalfGraphon

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Measure-preserving cut alignment transfers the two numerical
invariants without putting all input graphs on the same space. -/
theorem aligned_invariants (μ : Measure X) (ν : Measure Y) (π : Measure (X×Y))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hπ : π univ = 1)
    (hp : MeasurePreserving Prod.fst π μ) (hq : MeasurePreserving Prod.snd π ν)
    (W : Kernel X) (L : Kernel Y) (ε : ℝ)
    (hcut : CutBound π (pullKernel W Prod.fst measurable_fst) (pullKernel L Prod.snd measurable_snd) ε) :
    |beta μ W - beta ν L| ≤ ε/2 ∧
      |t3 μ W W W - t3 ν L L L| ≤ 3*ε := by
  have : IsFiniteMeasure π := ⟨by rw [hπ]; exact ENNReal.one_lt_top⟩
  have hm : mass π = 1 := by simp [mass, Measure.real, hπ]
  have hμ : mass μ = 1 := by rw [← hp.map_eq,map_mass Prod.fst measurable_fst,hm]
  have hν : mass ν = 1 := by rw [← hq.map_eq,map_mass Prod.snd measurable_snd,hm]
  constructor
  · have h := cut_beta π hm _ _ ε hcut
    rwa [beta_pull π μ _ hp hμ, beta_pull π ν _ hq hν] at h
  · have h := t3_cut π _ _ ε hcut
    rwa [pull_triangle _ _ _ _ π μ hp, pull_triangle _ _ _ _ π ν hq, hm, mul_one] at h

theorem aligned_sparse_limit {Z : ℕ → Type*} [∀ k, MeasurableSpace (Z k)]
    (μ : ∀ k, Measure (Z k)) [∀ k, IsFiniteMeasure (μ k)]
    (ν : Measure Y) [IsFiniteMeasure ν] (W : ∀ k, Kernel (Z k)) (L : Kernel Y)
    (b : ℝ) (hb : ∀ k, b ≤ beta (μ k) (W k))
    (ht : ∀ k, t3 (μ k) (W k) (W k) (W k) = 0)
    (ha : ∀ ε > 0, ∀ᶠ k in atTop, ∃ π : Measure (Z k × Y),
      MeasurePreserving Prod.fst π (μ k) ∧ MeasurePreserving Prod.snd π ν ∧ π univ = 1 ∧
      CutBound π (pullKernel (W k) Prod.fst measurable_fst)
        (pullKernel L Prod.snd measurable_snd) ε) :
    b ≤ beta ν L ∧ t3 ν L L L = 0 := by
  have close ε (he : 0 < ε) : ∃ k, |beta (μ k) (W k) - beta ν L| ≤ ε/2 ∧
      |t3 ν L L L| ≤ 3*ε := by
    obtain ⟨k,π,hp,hq,hπ,hcut⟩ := (ha ε he).exists
    obtain ⟨hb',ht'⟩ := aligned_invariants (μ k) ν π hπ hp hq (W k) L ε hcut
    rw [ht k,zero_sub,abs_neg] at ht'
    exact ⟨k,hb',ht'⟩
  constructor
  · by_contra! hn
    obtain ⟨k,hk,_⟩ := close (b-beta ν L) (sub_pos.mpr hn)
    have hk' := (abs_le.mp hk).2
    linarith [hb k]
  · by_contra hn
    have hh := abs_pos.mpr hn
    obtain ⟨_,_,ht'⟩ := close (|t3 ν L L L|/4) (by positivity)
    linarith

#print axioms aligned_sparse_limit
end SparseHalfGraphon
