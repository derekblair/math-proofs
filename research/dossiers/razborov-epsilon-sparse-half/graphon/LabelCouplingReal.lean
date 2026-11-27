import MatchedLabelCoupling
import CutExceptional
import TableDiagonal

open Set MeasureTheory Function Filter Topology
open scoped ENNReal BigOperators
namespace SparseHalfGraphon

variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

def labelMismatch (c : X → I) (d : Y → I) : Set (X × Y) := {z | c z.1 ≠ d z.2}

lemma labelMismatch_meas {c : X → I} {d : Y → I}
    (hc : Measurable c) (hd : Measurable d) : MeasurableSet (labelMismatch c d) := by
  have he : labelMismatch c d = ⋃ i : I, cell c i ×ˢ (cell d i)ᶜ := by
    ext z
    change (c z.1 ≠ d z.2) ↔ _
    simp only [mem_iUnion, mem_prod, mem_compl_iff]
    constructor
    · intro h
      exact ⟨c z.1,rfl,Ne.symm h⟩
    · rintro ⟨i,hi,hj⟩ h
      exact hj (h.symm.trans hi)
  rw [he]
  exact MeasurableSet.iUnion (fun i => (hc (measurableSet_singleton i)).prod
    (hd (measurableSet_singleton i)).compl)

lemma label_masses_sum (μ : Measure X) (c : X → I) (hc : Measurable c) :
    ∑ i, μ (cell c i) = μ univ := by
  have hs := congrArg (fun m : Measure X => m univ) (sum_label_restrict μ c hc)
  simpa only [Measure.sum_apply _ MeasurableSet.univ, Measure.restrict_apply_univ, tsum_fintype] using hs

theorem matched_label_coupling_real (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : μ univ = 1) (hn : ν univ = 1)
    (c : X → I) (d : Y → I) (hc : Measurable c) (hd : Measurable d) :
    ∃ π : Measure (X×Y), MeasurePreserving Prod.fst π μ ∧ MeasurePreserving Prod.snd π ν ∧
      π univ = 1 ∧
      π.real (labelMismatch c d) ≤ 1 - ∑ i, min (μ.real (cell c i)) (ν.real (cell d i)) := by
  obtain ⟨π,h₁,h₂,hπ⟩ := matched_label_coupling μ ν (hm.trans hn.symm) c d hc hd
  have hp : π univ = 1 := by
    rw [← hm, ← h₁.map_eq, Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ]
  have hb : (∑ i, min (μ (cell c i)) (ν (cell d i))) ≤ μ univ := by
    rw [← label_masses_sum μ c hc]
    exact Finset.sum_le_sum (fun _ _ => min_le_left _ _)
  have hM : μ univ ≠ ⊤ := measure_ne_top _ _
  have hfin : μ univ - (∑ i, min (μ (cell c i)) (ν (cell d i))) ≠ ⊤ :=
    ne_top_of_le_ne_top hM tsub_le_self
  refine ⟨π,h₁,h₂,hp,?_⟩
  have hr := ENNReal.toReal_mono hfin hπ
  rw [ENNReal.toReal_sub_of_le hb hM, hm, ENNReal.toReal_one, ENNReal.toReal_sum] at hr
  · simpa only [labelMismatch, Measure.real, ENNReal.toReal_min (measure_ne_top μ _) (measure_ne_top ν _)] using hr
  · intro i _
    exact ne_top_of_le_ne_top (measure_ne_top μ _) (min_le_left _ _)

#print axioms matched_label_coupling_real
end SparseHalfGraphon
