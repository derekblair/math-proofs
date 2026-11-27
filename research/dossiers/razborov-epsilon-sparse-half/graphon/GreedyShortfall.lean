import LowerMarkLimit
import GreedyEligible

open Set MeasureTheory Function Filter Topology
namespace SparseHalfGraphon

variable {X I : Type*} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- Replacing the grown mark by the original one incurs at most its
mass difference and the small shift of the greedy stopping threshold. -/
theorem greedy_shortfall (hμ : mass μ=1) (W : Kernel X)
    (c : X→I) (hc : Measurable c) (i : I) (B : Set X) (hB : MeasurableSet B)
    (hAB : cell c i⊆B)
    (hFloor : ∀ x∉B, 1/2-μ.real (cell c i)≤deg (μ.restrict B) W x) :
    (∫ x,outsideShortfall c i (deg (μ.restrict (cell c i)) W) (1/10) x ∂μ) ≤
      max 0 (μ.real B-2/5)+μ.real B-μ.real (cell c i) := by
  let A := cell c i
  let C := B\A
  let q := max 0 (μ.real B-2/5)
  let s := indicatorWeight C
  let d := deg (μ.restrict A) W
  let f := outsideShortfall c i d (1/10)
  have hA : MeasurableSet A := hc (measurableSet_singleton i)
  have hC : MeasurableSet C := hB.diff hA
  have hm : μ.real C=μ.real B-μ.real A := measureReal_sdiff hAB hA
  have hq : 0≤q := le_max_left _ _
  have hu := outsideShortfall_unit c hc i d (deg_measurable _ W) (deg_nonneg _ W) (1/10) (by norm_num)
  have hi : Integrable f μ := integrable_bounded _ hu.1 (fun x=>(hu.2 x).1) (fun x=>(hu.2 x).2)
  have hs := indicatorWeight_unit C hC
  have his : Integrable s μ := integrable_bounded _ hs.1 (fun x=>(hs.2 x).1) (fun x=>(hs.2 x).2)
  have H : ∀ x, f x≤q+s x := by
    intro x
    classical
    by_cases hx : x∈A
    · have h : x∉(cell c i)ᶜ := by simpa only [mem_compl_iff,not_not] using hx
      simp only [f,outsideShortfall,indicator_of_notMem h]
      linarith [hq,(hs.2 x).1]
    · by_cases hxb : x∈B
      · have hs1 : s x=1 := by
          change C.indicator (fun _=>1) x=1
          exact indicator_of_mem (show x ∈ C from ⟨hxb,hx⟩) _
        linarith [hq,(hu.2 x).2]
      · have hf : f x=max 0 (1/10-d x) := by
          exact indicator_of_mem hx _
        rw [hf]
        refine le_trans (max_le hq ?_) (le_add_of_nonneg_right (hs.2 x).1)
        have h := row_shift_point μ W B A hB hA x
        have h0 : A\B=∅ := diff_eq_empty.mpr hAB
        rw [h0,measureReal_empty,add_zero,hm] at h
        have hd := (abs_le.mp h).2
        have hfloor := hFloor x hxb
        have hq' : μ.real B-2/5≤q := le_max_right _ _
        change _ ≤ _ at hd
        change 1/10-deg (μ.restrict A) W x≤q
        linarith
  have hh := integral_mono hi ((integrable_const q).add his) H
  rw [integral_add' (integrable_const q) his,integral_const,smul_eq_mul] at hh
  change (∫ x,f x ∂μ)≤mass μ*q+(∫ x,s x ∂μ) at hh
  rw [hμ,one_mul,indicatorWeight_mass μ C hC,hm] at hh
  exact hh.trans_eq (by ring)

#print axioms greedy_shortfall
end SparseHalfGraphon
