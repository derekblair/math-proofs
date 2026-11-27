import ComplementAtoms
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set MeasureTheory Function
namespace SparseHalfGraphon

/-- A countable measurable generator can be closed under intersections
without losing countability. Include the whole anchor space explicitly. -/
theorem countable_generating_pi {X : Type*} [mx : MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] :
    ∃ T : ℕ → Set X, (∀ n, MeasurableSet (T n)) ∧
      mx = MeasurableSpace.generateFrom (range T) ∧ IsPiSystem (range T) ∧ univ ∈ range T := by
  classical
  let S := insert (univ : Set X) (MeasurableSpace.countableGeneratingSet X)
  have hS : S.Countable := (MeasurableSpace.countable_countableGeneratingSet (α:=X)).insert _
  have hSm (U : Set X) (h : U ∈ S) : MeasurableSet U := by
    rcases mem_insert_iff.mp h with rfl | h
    · exact MeasurableSet.univ
    · exact MeasurableSpace.measurableSet_countableGeneratingSet h
  let D := generatePiSystem S
  have hU : univ ∈ D := subset_generatePiSystem_self S (mem_insert _ _)
  have hD : D.Countable := by
    letI : Countable S := hS.to_subtype
    let F : Finset S → Set X := fun s => ⋂ z ∈ s, (z.val : Set X)
    apply (countable_range F).mono
    intro U h
    change U ∈ generatePiSystem S at h
    induction h using generatePiSystem_induction with
    | base U h =>
      refine ⟨{⟨U,h⟩},?_⟩
      ext x
      simp only [F,mem_iInter,Finset.mem_singleton]
      exact ⟨fun hx=>hx _ rfl,fun hx z hz=>hz.symm ▸ hx⟩
    | inter U V hU hV _ ihU ihV =>
      obtain ⟨a,ha⟩ := ihU
      obtain ⟨b,hb⟩ := ihV
      refine ⟨a∪b,?_⟩
      rw [← ha, ← hb]
      ext x
      simp only [F,mem_iInter,Finset.mem_union,mem_inter_iff]
      exact ⟨fun h => ⟨fun z hz => h z (Or.inl hz),fun z hz => h z (Or.inr hz)⟩,
        fun ⟨h1,h2⟩ z hz => hz.elim (h1 z) (h2 z)⟩
  let T := enumerateCountable hD univ
  have hT : range T = D := range_enumerateCountable_of_mem hD hU
  refine ⟨T,fun n => ?_,?_,?_,?_⟩
  · have ht : T n ∈ D := by rw [← hT]; exact mem_range_self n
    exact generatePiSystem_measurableSet hSm _ ht
  · rw [hT]
    apply le_antisymm
    · rw [← MeasurableSpace.generateFrom_countableGeneratingSet (α:=X)]
      apply MeasurableSpace.generateFrom_mono
      exact (subset_insert _ _).trans (subset_generatePiSystem_self S)
    · exact MeasurableSpace.generateFrom_le (generatePiSystem_measurableSet hSm)
  · rw [hT]
    exact isPiSystem_generatePiSystem S
  · rwa [hT]

#print axioms countable_generating_pi
end SparseHalfGraphon
