import MarkedGraphonCompactness
import ShiftedRows

open Set MeasureTheory Function Filter Topology
open scoped ENNReal symmDiff
namespace SparseHalfGraphon

variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (π : Measure (X×Y)) [IsFiniteMeasure π]

lemma mark_diff_subset (c : X→I) (d : Y→I) (i : I) :
    ((Prod.fst ⁻¹' cell c i) ∆ (Prod.snd ⁻¹' cell d i)) ⊆ labelMismatch c d := by
  intro z hz
  change c z.1 ≠ d z.2
  intro h
  have he : (z ∈ Prod.fst ⁻¹' cell c i) ↔ (z ∈ Prod.snd ⁻¹' cell d i) := by
    change (c z.1 = i) ↔ (d z.2 = i)
    rw [h]
  rcases hz with h' | h'
  · exact h'.2 (he.mp h'.1)
  · exact h'.2 (he.mpr h'.1)

lemma real_mass_pull {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]
    {μ : Measure Z} {ν : Measure V} {p : Z→V}
    (hp : MeasurePreserving p μ ν) {S : Set V} (hS : MeasurableSet S) :
    μ.real (p ⁻¹' S)=ν.real S := by
  unfold Measure.real
  rw [hp.measure_preimage hS.nullMeasurableSet]

lemma degree_pull_restricted {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]
    {μ : Measure Z} {ν : Measure V} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {p : Z→V}
    (hp : MeasurePreserving p μ ν) {S : Set V} (hS : MeasurableSet S) (K : Kernel V) (z : Z) :
    deg (μ.restrict (p ⁻¹' S)) (pullKernel K p hp.measurable) z =
      deg (ν.restrict S) K (p z) := by
  have hmap : (μ.restrict (p ⁻¹' S)).map p = ν.restrict S := by
    rw [← Measure.restrict_map hp.measurable hS, hp.map_eq]
  unfold deg
  rw [← hmap, integral_map hp.measurable.aemeasurable (rowMeasurable K (p z)).aestronglyMeasurable]
  rfl

theorem aligned_mark_mass (μ : Measure X) (ν : Measure Y)
    (hp : MeasurePreserving Prod.fst π μ) (hq : MeasurePreserving Prod.snd π ν)
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (c : X→I) (d : Y→I) (hc : Measurable c) (hd : Measurable d) (i : I) :
    |μ.real (cell c i) - ν.real (cell d i)| ≤ π.real (labelMismatch c d) := by
  have hS : MeasurableSet (cell c i) := hc (measurableSet_singleton i)
  have hT : MeasurableSet (cell d i) := hd (measurableSet_singleton i)
  rw [← real_mass_pull hp hS,← real_mass_pull hq hT]
  exact (abs_measureReal_sub_le_measureReal_symmDiff (μ:=π) (hp.measurable hS).nullMeasurableSet
    (hq.measurable hT).nullMeasurableSet).trans (measureReal_mono (μ:=π) (mark_diff_subset c d i))

theorem aligned_mark_degree (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hπ : mass π = 1)
    (hp : MeasurePreserving Prod.fst π μ) (hq : MeasurePreserving Prod.snd π ν)
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (c : X→I) (d : Y→I) (hc : Measurable c) (hd : Measurable d) (i : I)
    (W : Kernel X) (L : Kernel Y) (ε : ℝ)
    (hcut : CutBound π (pullKernel W Prod.fst measurable_fst)
      (pullKernel L Prod.snd measurable_snd) ε) :
    (∫ z, |deg (μ.restrict (cell c i)) W z.1 - deg (ν.restrict (cell d i)) L z.2| ∂π) ≤
      2*ε + π.real (labelMismatch c d) := by
  have hS : MeasurableSet (cell c i) := hc (measurableSet_singleton i)
  have hT : MeasurableSet (cell d i) := hd (measurableSet_singleton i)
  have hSp := hp.measurable hS
  have hTq := hq.measurable hT
  have h := shifted_cut_degree_L1 π _ _ (Prod.fst ⁻¹' cell c i)
    (Prod.snd ⁻¹' cell d i) hSp hTq ε hcut
  simp only [degree_pull_restricted hp hS, degree_pull_restricted hq hT, hπ, one_mul,
    ← measureReal_symmDiff_eq (μ:=π) hSp hTq] at h
  exact h.trans (add_le_add_right (measureReal_mono (μ:=π) (mark_diff_subset c d i)) _)

#print axioms aligned_mark_mass
#print axioms aligned_mark_degree
end SparseHalfGraphon
