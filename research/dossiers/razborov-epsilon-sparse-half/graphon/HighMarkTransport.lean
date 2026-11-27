import HighMarkFinite
import Mathlib.MeasureTheory.Measure.Continuity
open MeasureTheory Set Function Filter Topology
open scoped BigOperators ENNReal
namespace SparseHalfGraphon

section Threshold
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem highOutside_meas (K : Kernel X) {A : Set X} (h : MeasurableSet A) (t : ℝ) :
    MeasurableSet (highOutside μ K A t) := by
  exact h.compl.inter (measurableSet_lt measurable_const (deg_measurable _ K))

theorem tail_mass_integral (f : X → ℝ) (hf : Measurable f) (hi : Integrable f μ)
    (hn : ∀ x, 0 ≤ f x) (δ : ℝ) (hp : 0 < δ) :
    μ.real {x | δ ≤ f x} ≤ (∫ x,f x ∂μ)/δ := by
  let E := {x | δ ≤ f x}
  have hm : MeasurableSet E := measurableSet_le measurable_const hf
  have hh : (∫ x in E, δ ∂μ) ≤ ∫ x in E, f x ∂μ := by
    exact setIntegral_mono_on (integrable_const δ) hi.integrableOn hm (fun x hx => hx)
  have hh' : (∫ x in E, f x ∂μ) ≤ ∫ x, f x ∂μ := by
    rw [← integral_indicator hm]
    apply integral_mono (hi.indicator hm) hi
    intro x
    by_cases hx : x∈E <;> simp [hx,hn x]
  simp only [setIntegral_const,smul_eq_mul] at hh
  exact (le_div_iff₀ hp).mpr (hh.trans hh')
end Threshold

variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace I] [MeasurableSingletonClass I]

/-- A positive threshold margin permits transport of a high outside set.
The estimate charges the mark mismatch once and the high row error tail once. -/
theorem highOutside_aligned (μ : Measure X) (ν : Measure Y) (π : Measure (X×Y))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure π] (hπ : mass π = 1)
    (hp : MeasurePreserving Prod.fst π μ) (hq : MeasurePreserving Prod.snd π ν)
    (c : X → I) (d : Y → I) (hc : Measurable c) (hd : Measurable d) (i : I)
    (K : Kernel X) (L : Kernel Y) (ε δ : ℝ) (hδ : 0 < δ)
    (hm : π.real (labelMismatch c d) ≤ δ)
    (hcut : CutBound π (pullKernel K Prod.fst measurable_fst)
      (pullKernel L Prod.snd measurable_snd) ε) :
    ν.real (highOutside ν L (cell d i) (ν.real (cell d i)/2+δ)) ≤
      μ.real (highOutside μ K (cell c i) (μ.real (cell c i)/2)) +
      π.real (labelMismatch c d) + (2*ε+π.real (labelMismatch c d))/(δ/2) := by
  let A := cell c i
  let B := cell d i
  let g := deg (μ.restrict A) K
  let h := deg (ν.restrict B) L
  have hA : MeasurableSet A := hc (measurableSet_singleton i)
  have hB : MeasurableSet B := hd (measurableSet_singleton i)
  let P := highOutside μ K A (μ.real A/2)
  let Q := highOutside ν L B (ν.real B/2+δ)
  have hP : MeasurableSet P := highOutside_meas μ K hA _
  have hQ : MeasurableSet Q := highOutside_meas ν L hB _
  let f (z : X×Y) := |g z.1-h z.2|
  have mf : Measurable f := continuous_abs.measurable.comp (((deg_measurable _ K).comp measurable_fst).sub
    ((deg_measurable _ L).comp measurable_snd))
  have fi : Integrable f π := by
    apply integrable_bounded π mf (fun _ => abs_nonneg _)
      (C := mass (μ.restrict A)+mass (ν.restrict B))
    intro z
    apply abs_le.mpr
    have g₁ := deg_le_mass (μ.restrict A) K z.1
    have h₁ := deg_le_mass (ν.restrict B) L z.2
    have g₀ := deg_nonneg (μ.restrict A) K z.1
    have h₀ := deg_nonneg (ν.restrict B) L z.2
    change g z.1 ≤ _ at g₁
    change 0 ≤ g z.1 at g₀
    change h z.2 ≤ _ at h₁
    change 0 ≤ h z.2 at h₀
    have a : 0 ≤ mass (μ.restrict A) := measureReal_nonneg
    have b : 0 ≤ mass (ν.restrict B) := measureReal_nonneg
    exact ⟨by linarith,by linarith⟩
  let Err := {z : X×Y | δ/2 ≤ f z}
  let M := labelMismatch c d
  have masserr := aligned_mark_mass π μ ν hp hq c d hc hd i
  have massUp : μ.real A ≤ ν.real B+δ := by
    have H := (le_abs_self (μ.real A-ν.real B)).trans (masserr.trans hm)
    linarith
  have sub : Prod.snd ⁻¹' Q ⊆ (Prod.fst ⁻¹' P ∪ M) ∪ Err := by
    intro z hz
    by_cases E : z ∈ Err
    · exact Or.inr E
    · refine Or.inl ?_
      by_cases H : z ∈ M
      · exact Or.inr H
      · refine Or.inl ?_
        have eq : c z.1 = d z.2 := by
          by_contra hn
          exact H hn
        have outside : z.1 ∉ A := by
          intro H'
          exact hz.1 (eq.symm.trans H')
        have high : ν.real B/2+δ < h z.2 := hz.2
        have lowError : f z < δ/2 := lt_of_not_ge E
        have lower : h z.2-g z.1 ≤ f z := by
          simpa only [f,neg_sub] using neg_le_abs (g z.1-h z.2)
        change z.1 ∉ A ∧ μ.real A/2 < g z.1
        exact ⟨outside,by linarith⟩
  have ff : (∫ z,f z ∂π) ≤ 2*ε+π.real M :=
    aligned_mark_degree π μ ν hπ hp hq c d hc hd i K L ε hcut
  have tail : π.real Err ≤ (2*ε+π.real M)/(δ/2) :=
    (tail_mass_integral π f mf fi (fun _ => abs_nonneg _) _ (by linarith)).trans
      (div_le_div_of_nonneg_right ff (by linarith))
  rw [← real_mass_pull hq hQ,← real_mass_pull hp hP]
  calc
    _ ≤ π.real ((Prod.fst ⁻¹' P ∪ M) ∪ Err) := measureReal_mono sub
    _ ≤ π.real (Prod.fst ⁻¹' P ∪ M)+π.real Err := measureReal_union_le _ _
    _ ≤ _ := add_le_add (measureReal_union_le _ _) tail

#print axioms highOutside_aligned
end SparseHalfGraphon
