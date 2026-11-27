import MatchedCoupling
import ProfileUniqueness
import Mathlib.MeasureTheory.Measure.Sub

open MeasureTheory Set Function
open scoped ENNReal
namespace SparseHalfGraphon

variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

noncomputable def takeMass {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (S : Set Z) (a : ℝ≥0∞) : Measure Z := (a/(μ S)) • μ.restrict S

lemma takeMass_univ {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsFiniteMeasure μ] (S:Set Z) (a:ℝ≥0∞) (ha:a≤μ S) :
    takeMass μ S a univ=a := by
  by_cases hz : μ S=0
  · have ha0 : a=0 := le_antisymm (hz ▸ ha) bot_le
    simp [takeMass,ha0]
  · unfold takeMass
    rw [Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ,
      ENNReal.div_mul_cancel hz (measure_ne_top μ S)]

lemma takeMass_le {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsFiniteMeasure μ] (S:Set Z) (a:ℝ≥0∞) (ha:a≤μ S) :
    takeMass μ S a≤μ.restrict S := by
  by_cases hz : μ S=0
  · have ha0 : a=0 := le_antisymm (hz ▸ ha) bot_le
    simp [takeMass,ha0,hz]
    exact bot_le
  · have hdiv : a/μ S≤1 := by
      exact (ENNReal.div_le_iff_le_mul (Or.inl hz) (Or.inl (measure_ne_top μ S))).mpr
        (by simpa using ha)
    intro U
    change ((a/μ S) • μ.restrict S) U≤μ.restrict S U
    rw [Measure.smul_apply,smul_eq_mul]
    calc
      _≤1*(μ.restrict S U) := by gcongr
      _=_ := one_mul _

lemma sum_label_restrict {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (c:Z→I) (hc:Measurable c) :
    Measure.sum (fun i => μ.restrict (cell c i))=μ := by
  have hd : Pairwise (Disjoint on cell c) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hij ((show c x=i from hx).symm.trans (show c x=j from hy))
  have hu : (⋃ i, cell c i)=univ := by
    ext x
    simp [cell]
  rw [← Measure.restrict_iUnion hd (fun i => hc (measurableSet_singleton i)),hu,Measure.restrict_univ]

lemma takeMass_mismatches_zero (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c:X→I) (d:Y→I)
    (hc:Measurable c) (hd:Measurable d) (i:I) (a:ℝ≥0∞)
    (ha:a≤μ (cell c i)) (hb:a≤ν (cell d i)) :
    joinPiece (takeMass μ (cell c i) a) (takeMass ν (cell d i) a)
      {z:X×Y | c z.1≠d z.2}=0 := by
  let μi := takeMass μ (cell c i) a
  let νi := takeMass ν (cell d i) a
  have lm : μi≤μ.restrict (cell c i) := takeMass_le μ _ _ ha
  have ln : νi≤ν.restrict (cell d i) := takeMass_le ν _ _ hb
  have iν : IsFiniteMeasure (ν.restrict (cell d i)) := inferInstance
  have : IsFiniteMeasure νi := isFiniteMeasure_of_le _ ln
  have hsub := Measure.prod_mono lm ln
  have hs : {z:X×Y | c z.1≠d z.2} ⊆ (cell c i ×ˢ cell d i)ᶜ := by
    intro z hz
    change ¬ (c z.1=i ∧ d z.2=i)
    intro h
    exact hz (h.1.trans h.2.symm)
  have hz : ((μ.restrict (cell c i)).prod (ν.restrict (cell d i)))
      {z:X×Y | c z.1≠d z.2}=0 := by
    rw [Measure.prod_restrict]
    have he : (μ.prod ν).restrict (cell c i ×ˢ cell d i) ((cell c i ×ˢ cell d i)ᶜ)=0 := by
      have hm : MeasurableSet (cell c i ×ˢ cell d i) :=
        (hc (measurableSet_singleton i)).prod (hd (measurableSet_singleton i))
      rw [Measure.restrict_apply hm.compl,Set.compl_inter_self,measure_empty]
    exact le_antisymm ((measure_mono hs).trans_eq he) bot_le
  have h0 := le_antisymm ((hsub _).trans_eq hz) bot_le
  change ((νi univ)⁻¹ • (μi.prod νi)) _=0
  rw [Measure.smul_apply,h0,smul_zero]

/-- Couple two finite marked partitions by matching exactly the min mass
at each label and placing only the leftover mass on possible mismatches. -/
theorem matched_label_coupling (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hmass : μ univ=ν univ)
    (c:X→I) (d:Y→I) (hc : Measurable c) (hd : Measurable d) :
    ∃ π : Measure (X×Y), MeasurePreserving Prod.fst π μ ∧
      MeasurePreserving Prod.snd π ν ∧
      π {z:X×Y | c z.1≠d z.2} ≤
        μ univ-∑ i, min (μ (cell c i)) (ν (cell d i)) := by
  classical
  let w : I→ℝ≥0∞ := fun i=>min (μ (cell c i)) (ν (cell d i))
  let a : I→Measure X := fun i=>takeMass μ (cell c i) (w i)
  let b : I→Measure Y := fun i=>takeMass ν (cell d i) (w i)
  have ha i : a i≤μ.restrict (cell c i) := takeMass_le μ _ _ (min_le_left _ _)
  have hb i : b i≤ν.restrict (cell d i) := takeMass_le ν _ _ (min_le_right _ _)
  have : ∀ i, IsFiniteMeasure (a i) := fun i=>isFiniteMeasure_of_le _ (ha i)
  have : ∀ i, IsFiniteMeasure (b i) := fun i=>isFiniteMeasure_of_le _ (hb i)
  have haMass (i:I) : a i univ=w i := takeMass_univ μ _ _ (min_le_left _ _)
  have hbMass (i:I) : b i univ=w i := takeMass_univ ν _ _ (min_le_right _ _)
  have hsa : Measure.sum a≤μ := by
    rw [← sum_label_restrict μ c hc]
    intro S
    rw [Measure.sum_apply_of_countable,Measure.sum_apply_of_countable]
    exact ENNReal.tsum_le_tsum (fun i=>ha i S)
  have hsb : Measure.sum b≤ν := by
    rw [← sum_label_restrict ν d hd]
    intro S
    rw [Measure.sum_apply_of_countable,Measure.sum_apply_of_countable]
    exact ENNReal.tsum_le_tsum (fun i=>hb i S)
  have : IsFiniteMeasure (Measure.sum a) := isFiniteMeasure_of_le _ hsa
  have : IsFiniteMeasure (Measure.sum b) := isFiniteMeasure_of_le _ hsb
  let a₀:=μ-Measure.sum a
  let b₀:=ν-Measure.sum b
  have : IsFiniteMeasure a₀ := isFiniteMeasure_of_le μ (fun S => Measure.sub_le S)
  have : IsFiniteMeasure b₀ := isFiniteMeasure_of_le ν (fun S => Measure.sub_le S)
  have hSa : (Measure.sum a) univ=∑ i,w i := by
    rw [Measure.sum_apply _ MeasurableSet.univ,tsum_fintype]
    simp only [haMass]
  have hSb : (Measure.sum b) univ=∑ i,w i := by
    rw [Measure.sum_apply _ MeasurableSet.univ,tsum_fintype]
    simp only [hbMass]
  have hleft : a₀ univ=b₀ univ := by
    unfold a₀ b₀
    rw [Measure.sub_apply MeasurableSet.univ hsa,Measure.sub_apply MeasurableSet.univ hsb,
      hSa,hSb,hmass]
  let ρ := Measure.sum (fun i=>joinPiece (a i) (b i))
  let σ := joinPiece a₀ b₀
  have hρ := join_family a b (fun i => (haMass i).trans (hbMass i).symm)
  have hσ₁ : σ.map Prod.fst=a₀ := joinPiece_fst _ _ hleft
  have hσ₂ : σ.map Prod.snd=b₀ := joinPiece_snd _ _ hleft
  let π := σ+ρ
  refine ⟨π,⟨measurable_fst,?_⟩,⟨measurable_snd,?_⟩,?_⟩
  · unfold π
    rw [Measure.map_add _ _ measurable_fst,hσ₁,hρ.1.map_eq]
    exact Measure.sub_add_cancel_of_le hsa
  · unfold π
    rw [Measure.map_add _ _ measurable_snd,hσ₂,hρ.2.map_eq]
    exact Measure.sub_add_cancel_of_le hsb
  · let M : Set (X×Y) := {z|c z.1≠d z.2}
    have hm : MeasurableSet M := by
      have he : M=⋃ i:I, cell c i ×ˢ (cell d i)ᶜ := by
        ext z
        change (c z.1≠d z.2)↔_
        simp only [mem_iUnion,mem_prod,mem_compl_iff]
        constructor
        · intro h
          exact ⟨c z.1,rfl,Ne.symm h⟩
        · rintro ⟨i,hi,hj⟩ h
          exact hj (h.symm.trans hi)
      rw [he]
      exact MeasurableSet.iUnion (fun i=>(hc (measurableSet_singleton i)).prod
        (hd (measurableSet_singleton i)).compl)
    have hρ0 : ρ M=0 := by
      unfold ρ
      rw [Measure.sum_apply _ hm]
      have he (i:I) : joinPiece (a i) (b i) M=0 :=
        takeMass_mismatches_zero μ ν c d hc hd i (w i) (min_le_left _ _) (min_le_right _ _)
      simp only [he,tsum_zero]
    change π M≤μ univ-∑ i,w i
    unfold π
    rw [Measure.add_apply _ _ M,hρ0,add_zero]
    have hs : σ univ=a₀ univ := by
      rw [← hσ₁,Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ]
    calc
      σ M≤σ univ := measure_mono (subset_univ _)
      _=a₀ univ := hs
      _=_ := by unfold a₀; rw [Measure.sub_apply MeasurableSet.univ hsa,hSa]

#print axioms matched_label_coupling
end SparseHalfGraphon
