import GeometricProductConditioning

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset
open scoped ENNReal
variable {S I : Type*} [MeasurableSpace S] [Fintype I] [DecidableEq I]

def labelSlices (A : Set S) (L : Finset I) (i : I) : Set S :=
  if i ∈ L then A else Aᶜ

def keepLabels (L : Finset I) (x : I → S) : {i : I // i ∈ L} → S :=
  fun i => x i

theorem keepLabels_measurePreserving (σ : Measure S) [IsProbabilityMeasure σ] (A : Set S)
    (a0 : σ A ≠ 0) (a1 : σ Aᶜ ≠ 0) (L : Finset I) :
    MeasurePreserving (keepLabels L)
      (Measure.pi (fun i => condOn σ (labelSlices A L i)))
      (Measure.pi (fun _ : {i : I // i ∈ L} => condOn σ A)) := by
  let μ (i : I) := condOn σ (labelSlices A L i)
  letI (i : I) : IsProbabilityMeasure (μ i) := by
    apply condOn_probability
    · by_cases hi : i ∈ L <;> simp [labelSlices, hi, μ, a0, a1]
    · exact measure_ne_top σ _
  have hm := measurePreserving_fst.comp
      (measurePreserving_piEquivPiSubtypeProd μ (fun i => i ∈ L))
  have hf : @Subtype.fintype I (fun i => i ∈ L) _ _ =
      Finset.Subtype.fintype L := Subsingleton.elim _ _
  rw [hf] at hm
  change MeasurePreserving (keepLabels L) (Measure.pi μ)
    (Measure.pi (fun i : {i : I // i ∈ L} => μ i)) at hm
  simpa only [μ, labelSlices, Subtype.prop, if_pos] using hm

/-- The exact law of a fixed retained set, including its unnormalized weight. -/
theorem keepLabels_selected_event (σ : Measure S) [IsProbabilityMeasure σ] (A : Set S)
    (a0 : σ A ≠ 0) (a1 : σ Aᶜ ≠ 0) (L : Finset I)
    (B : Set ({i : I // i ∈ L} → S)) (hB : MeasurableSet B) :
    (Measure.pi (fun _ : I => σ)).restrict (Set.univ.pi (labelSlices A L))
        ((keepLabels L) ⁻¹' B) =
      (∏ i, σ (labelSlices A L i)) *
        (Measure.pi (fun _ : {i : I // i ∈ L} => condOn σ A)) B := by
  have hp := keepLabels_measurePreserving σ A a0 a1 L
  rw [show (Measure.pi (fun _ : I => σ)).restrict (Set.univ.pi (labelSlices A L)) =
      (∏ i, σ (labelSlices A L i)) • Measure.pi (fun i => condOn σ (labelSlices A L i))
      from bernoulli_label_conditioning σ A a0 a1 L]
  rw [Measure.smul_apply, smul_eq_mul, hp.measure_preimage hB.nullMeasurableSet]

theorem keepLabels_mass_formula (σ : Measure S) (A : Set S) (L : Finset I) :
    (∏ i, σ (labelSlices A L i)) = (σ A)^L.card * (σ Aᶜ)^(Fintype.card I - L.card) := by
  simp only [labelSlices, apply_ite (fun s => σ s), Finset.prod_ite, filter_mem_eq_inter,
    Finset.univ_inter, ← sdiff_eq_filter, Finset.prod_const, Finset.card_sdiff_of_subset
      (Finset.subset_univ L), Finset.card_univ]

#print axioms keepLabels_selected_event
#print axioms keepLabels_mass_formula
end RobustFolkman.GeometricGap
