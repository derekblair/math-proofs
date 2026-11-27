import RestrictedAllocations
import ComplementedAllocation
import LargeLow

open Set MeasureTheory Filter Function
open scoped ENNReal
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- The low-degree part of a near-endpoint obstructing limit vanishes.
O is a full-measure outside representative on which the transported
degree floor and total cap hold pointwise. -/
theorem endpoint_saturation (W : Kernel X) (A O : Set X)
    (hA : MeasurableSet A) (hO : MeasurableSet O) (hAO : Disjoint A O)
    (hAm : μ.real A=2/5) (hOm : μ.real O=3/5)
    (hAI : energyPair μ W (indicatorWeight A) (indicatorWeight A)=0)
    (ht : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle W z=0)
    (hb : 1/50 ≤ beta μ W)
    (hdeg : ∀ x∈O, 1/10≤deg (μ.restrict A) W x)
    (hcap : ∀ x∈O, deg μ W x≤2/5)
    (hEligible : 1/5≤μ.real (O∩{x | deg (μ.restrict A) W x≤1/5})) :
    μ.real (O∩{x | deg (μ.restrict A) W x<1/5})=0 := by
  let ν := μ.restrict A
  let a := indicatorWeight A
  let S := O ∩ {x | deg ν W x≤1/5}
  let L := O ∩ {x | deg ν W x<1/5}
  let U := O \ L
  let E := U ∩ S
  let ω := μ.restrict U
  have hν : mass ν=2/5 := by simpa [ν,mass,measureReal_restrict_apply_univ] using hAm
  have ha : Measurable a := measurable_const.indicator hA
  have ha0 (x) : 0≤a x := by
    classical
    by_cases hx:x∈A <;> simp [a,indicatorWeight,hx]
  have ha1 (x) : a x≤1 := by
    classical
    by_cases hx:x∈A <;> simp [a,indicatorWeight,hx]
  have haM : (∫ x,a x ∂μ)=2/5 := by
    simpa [a,indicatorWeight,integral_indicator hA,setIntegral_const,smul_eq_mul] using hAm
  have har : reweight μ a=ν := indicatorWeight_reweight μ A hA
  have hmS : MeasurableSet S := hO.inter (measurableSet_le (deg_measurable ν W) measurable_const)
  have hmL : MeasurableSet L := hO.inter (measurableSet_lt (deg_measurable ν W) measurable_const)
  have hmU : MeasurableSet U := hO.diff hmL
  have hmE : MeasurableSet E := hmU.inter hmS
  have hLS : L⊆S := by
    intro x hx
    have hd : deg ν W x < 1/5 := hx.2
    exact ⟨hx.1, hd.le⟩
  have hL0 : L⊆O := inter_subset_left
  have hSa (x) (hx:x∈S) : a x=0 := by
    classical
    have hn : x∉A := fun hv=>Set.disjoint_left.mp hAO hv hx.1
    simp [a,indicatorWeight,hn]
  have hSd (x) (hx:x∈S) : 1/10≤deg (reweight μ a) W x ∧ deg (reweight μ a) W x≤1/5 := by
    rw [har]
    exact ⟨hdeg x hx.1,hx.2⟩
  have hLd (x) (hx:x∈L) : deg (reweight μ a) W x<1/5 := har.symm ▸ hx.2
  have hLc : μ.real L<1/10 :=
    large_low_impossible μ W a ha ha0 ha1 haM hAI ht hb S L hmS hmL hLS hSa hSd hLd
      hEligible
  by_contra hz
  have hLp : 0<μ.real L := lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
  have hUm : ω.real U=3/5-μ.real L := by
    rw [restrict_real_sub μ U U hmU subset_rfl]
    exact (measureReal_sdiff hL0 hmL).trans (by rw [hOm])
  have hrows : ∀ᵐ x ∂ω, mass ν/2≤deg ν W x := by
    have hu := ae_restrict_mem (μ:=μ) hmU
    filter_upwards [hu] with x hx
    rw [hν]
    by_contra! hv
    exact hx.2 ⟨hx.1,by change deg ν W x<1/5; linarith⟩
  have hνa : ν ≪ μ := Measure.restrict_le_self.absolutelyContinuous
  have hωa : ω ≪ μ := Measure.restrict_le_self.absolutelyContinuous
  have hnonnull : ν univ ≠ 0 := by
    intro hn
    change (ν univ).toReal=2/5 at hν
    norm_num [hn] at hν
  obtain ⟨T,hmT,hgT,hpT,huT⟩ := countable_generating_pi (X:=X)
  obtain ⟨ι,hcount,hinh,P,Q,hmP,hmQ,hSub,hinner,houter,hsupp,hrow⟩ :=
    paired_profile_cells ω ν W T hmT hgT hpT huT hnonnull E hmE
      (edge_complement μ ν ω hνa hωa W ht hrows)
  letI : Countable ι := hcount
  letI : Nonempty ι := hinh
  let b := ∑' j, cellCapacity ω P Q j
  have heU (j) : P j ∪ Q j⊆U := (hSub j).trans inter_subset_left
  have hUsupp : ∀ᵐ z ∂ω.prod ω, z.1∈U → z.2∈U → 0<W.W z →
      ∃ j, (z.1∈P j ∧ z.2∈Q j) ∨ (z.1∈Q j ∧ z.2∈P j) := by
    filter_upwards [hsupp,outside_edges_equal_degree μ ν ω hνa hωa W ht hrows]
      with z hsp hh hz1 hz2 hw
    rcases hh with hzero | ⟨ha₁,ha₂⟩
    · exact False.elim (hw.ne' hzero)
    · have he1 : z.1∈E := ⟨hz1,hz1.1,by change deg ν W z.1≤1/5; rw [ha₁,hν]; norm_num⟩
      have he2 : z.2∈E := ⟨hz2,hz2.1,by change deg ν W z.2≤1/5; rw [ha₂,hν]; norm_num⟩
      exact hsp he1 he2 hw
  by_cases hEnough : 1/5-μ.real L ≤ 2*b
  · obtain ⟨F,hFm,hFu,hFoff,_,hFmass,hFrow⟩ :=
      paired_fractional_allocation ω W P Q hmP hmQ hinner houter
        (1/5-μ.real L) (by linarith) hEnough
    have fOff : ∀ x∉S\L, F x=0 := by
      intro x hx
      apply hFoff x
      intro h
      obtain ⟨j,hj⟩ := mem_iUnion.mp h
      have hh := hSub j hj
      exact hx ⟨hh.2,hh.1.2⟩
    have fOffU : ∀ x∉U, F x=0 := fun _ hx => hFoff _ (fun h=>hx ((iUnion_subset heU) h))
    have fMass : (∫ x,F x ∂μ)=1/5-μ.real L := by
      rwa [← supported_integral_restrict μ U hmU F fOffU]
    have fLoad : ∀ᵐ v ∂reweight μ a, load μ W F v≤1/10 := by
      rw [har]
      filter_upwards [hrow] with v hv
      rw [← supported_load_restrict μ U hmU W F fOffU v,hFrow v hv]
      linarith
    exact small_low_balanced_impossible μ W a ha ha0 ha1 haM hAI ht hb S L hmS hmL
      hLS hSa hSd hLd hLp F hFm (fun x=>(hFu x).1) (fun x=>(hFu x).2)
      fOff fMass fLoad
  · obtain ⟨I,hmI,hIU,hIm,hInd⟩ :=
      paired_independent_dual ω W U hmU P Q hmP hmQ heU houter hUsupp
    have hi : 1/2-μ.real L/2<μ.real I := by
      rw [restrict_real_sub μ U I hmI hIU] at hIm
      rw [hUm] at hIm
      change μ.real I=3/5-μ.real L-b at hIm
      linarith only [hIm,lt_of_not_ge hEnough]
    have hIL : Disjoint I L := Set.disjoint_left.mpr (fun _ hx hy=>(hIU hx).2 hy)
    have hIA : Disjoint A I := hAO.mono_right (hIU.trans sdiff_subset)
    have hId : ∀ x∈L, deg (μ.restrict I) W x≤3/10 := by
      intro x hx
      have hh := degree_disjoint_cap μ A I hA hmI hIA W x
      linarith [hcap x hx.1,hdeg x hx.1]
    exact (not_lt_of_ge hb) (small_low_independent_fill μ W I L hmI hmL hIL hLc hi
      (zero_rectangle_restrict_lift μ U I hmU hmI hIU W hInd) hId)

#print axioms endpoint_saturation
end SparseHalfGraphon
