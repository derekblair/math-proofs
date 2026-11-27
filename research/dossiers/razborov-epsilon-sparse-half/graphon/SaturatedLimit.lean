import EndpointSaturation

open Set MeasureTheory Filter Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- All special cut-limit hypotheses imply saturation a.e. off the mark.
The only non-closed input is the high-degree set measure cap, to be
obtained from independence in the actual finite approximants. -/
theorem saturated_limit (hμ : mass μ=1) (W : Kernel X) (A : Set X)
    (hA : MeasurableSet A) (hAm : μ.real A=2/5)
    (hAI : energyPair μ W (indicatorWeight A) (indicatorWeight A)=0)
    (ht : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle W z=0)
    (hb : 1/50 ≤ beta μ W)
    (hdeg : ∀ᵐ x ∂μ, x∉A → 1/10≤deg (μ.restrict A) W x)
    (hcap : ∀ᵐ x ∂μ, deg μ W x≤2/5)
    (hHigh : μ.real (Aᶜ∩{x | 1/5<deg (μ.restrict A) W x})≤2/5) :
    ∀ᵐ x ∂μ, x∉A → 1/5≤deg (μ.restrict A) W x := by
  let ν := μ.restrict A
  let O : Set X := Aᶜ∩{x | 1/10≤deg ν W x ∧ deg μ W x≤2/5}
  have hO : MeasurableSet O := hA.compl.inter
    ((measurableSet_le measurable_const (deg_measurable ν W)).inter
      (measurableSet_le (deg_measurable μ W) measurable_const))
  have hAO : Disjoint A O :=
    Set.disjoint_left.mpr (fun _ h1 h2 => h2.1 h1)
  have hOae : O =ᵐ[μ] Aᶜ := by
    filter_upwards [hdeg,hcap] with x hd hu
    apply propext
    exact ⟨fun ho=>ho.1,fun h=>⟨h,hd h,hu⟩⟩
  have hOm : μ.real O=3/5 := by
    have he := congrArg (fun r => r.toReal) (measure_congr hOae)
    change μ.real O=μ.real Aᶜ at he
    linarith [mass_compl_add μ A hA]
  have hd : ∀ x∈O, 1/10≤deg ν W x := fun _ h=>h.2.1
  have hu : ∀ x∈O, deg μ W x≤2/5 := fun _ h=>h.2.2
  let H := O ∩ {x | 1/5<deg ν W x}
  have hHm : MeasurableSet H := hO.inter (measurableSet_lt measurable_const (deg_measurable ν W))
  have hHsub : H ⊆ Aᶜ∩{x | 1/5<deg ν W x} := fun _ h =>⟨h.1.1,h.2⟩
  have hH : μ.real H≤2/5 := (measureReal_mono (μ:=μ) hHsub).trans hHigh
  have hdif : O\H = O∩{x | deg ν W x≤1/5} := by
    ext x
    change (x∈O ∧ ¬(x∈O ∧ 1/5<deg ν W x)) ↔ (x∈O ∧ deg ν W x≤1/5)
    exact ⟨fun ⟨hx,hy⟩=>⟨hx,le_of_not_gt (fun h=>hy ⟨hx,h⟩)⟩,
      fun ⟨hx,hy⟩=>⟨hx,fun h=>(not_lt_of_ge hy) h.2⟩⟩
  have hep : 1/5≤μ.real (O∩{x | deg ν W x≤1/5}) := by
    rw [← hdif,measureReal_sdiff inter_subset_left hHm,hOm]
    linarith
  have hz := endpoint_saturation μ W A O hA hO hAO hAm hOm hAI ht hb hd hu hep
  let D := O∩{x | deg ν W x<1/5}
  have hn : μ D=0 := (measureReal_eq_zero_iff).mp hz
  have hNo : ∀ᵐ x ∂μ, x∉D := ae_iff.mpr (by simpa only [not_not,setOf_mem_eq] using hn)
  filter_upwards [hOae,hNo] with x hx hnx ha
  have ho : x∈O := (Iff.of_eq hx).mpr ha
  by_contra! hlt
  exact hnx ⟨ho,hlt⟩

#print axioms saturated_limit
end SparseHalfGraphon
