import GeometricCapSelection

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset
open scoped ENNReal
variable {S I : Type*} [MeasurableSpace S] [Fintype I] [DecidableEq I]

noncomputable def retained (A : Set S) (x : I → S) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => x i ∈ A)

theorem retained_iff (A : Set S) (L : Finset I) (x : I → S) :
    retained A x = L ↔ x ∈ Set.univ.pi (labelSlices A L) := by
  classical
  rw [Finset.ext_iff]
  simp only [retained, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_pi,
    labelSlices]
  constructor
  · intro h i _
    by_cases hi : i ∈ L
    · simpa only [if_pos hi] using (h i).2 hi
    · simpa only [if_neg hi, Set.mem_compl_iff] using mt (h i).1 hi
  · intro h i
    have q := h i (Set.mem_univ i)
    by_cases hi : i ∈ L
    · exact iff_of_true (by simpa only [if_pos hi] using q) hi
    · exact iff_of_false (by simpa only [if_neg hi, Set.mem_compl_iff] using q) hi

theorem retained_partition (A : Set S) (k : ℕ) :
    {x : I → S | (retained A x).card = k} =
      ⋃ L ∈ (Finset.univ : Finset I).powersetCard k, Set.univ.pi (labelSlices A L) := by
  classical
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard, Finset.subset_univ,
    true_and, ← retained_iff]
  exact ⟨fun h => ⟨retained A x, h, rfl⟩, fun ⟨L,h,eq⟩ => eq.symm ▸ h⟩

theorem retained_count_distribution (σ : Measure S) [IsProbabilityMeasure σ] (A : Set S)
    (hA : MeasurableSet A) (k : ℕ) :
    (Measure.pi (fun _ : I => σ)) {x : I → S | (retained A x).card = k} =
      (Fintype.card I).choose k * ((σ A)^k * (σ Aᶜ)^(Fintype.card I - k)) := by
  classical
  have meas (L : Finset I) (i : I) : MeasurableSet (labelSlices A L i) := by
    by_cases hi : i ∈ L <;> simp [labelSlices, hi, hA, hA.compl]
  have disj : (↑((Finset.univ : Finset I).powersetCard k) : Set (Finset I)).PairwiseDisjoint
      (fun L => Set.univ.pi (labelSlices A L)) := by
    intro L _ K _ h
    change Disjoint (Set.univ.pi (labelSlices A L)) (Set.univ.pi (labelSlices A K))
    rw [Set.disjoint_left]
    intro x hx hy
    exact h ((retained_iff A L x).2 hx |>.symm.trans ((retained_iff A K x).2 hy))
  rw [retained_partition, measure_biUnion_finset disj (fun L _ => MeasurableSet.pi
    Set.countable_univ (fun i _ => meas L i))]
  simp only [Measure.pi_pi, keepLabels_mass_formula]
  rw [Finset.sum_congr rfl (fun L hL => show _ =
    (fun _ : Finset I => (σ A)^k * (σ Aᶜ)^(Fintype.card I-k)) L from by
    simp only [(Finset.mem_powersetCard.mp hL).2])]
  simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]

#print axioms retained_count_distribution
end RobustFolkman.GeometricGap
