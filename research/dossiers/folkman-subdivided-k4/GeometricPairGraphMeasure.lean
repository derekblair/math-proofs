import GeometricRootedSample

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset
open scoped ENNReal InnerProductSpace
variable {J S : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace S]

theorem measurable_sample_predicate_edge (A : Set (S×S)) (am : MeasurableSet A) (e : Finset J) :
    MeasurableSet {x : J→S | e∈samplePredicateGraph A x} := by
  classical
  have eq : {x : J→S | e∈samplePredicateGraph A x}
      = ⋃ i : J, ⋃ j : J,
          {x : J→S | i≠j ∧ (x i,x j)∈A ∧ ({i,j}:Finset J)=e} := by
    ext x
    simp only [mem_ofPred_eq,Set.mem_iUnion,samplePredicate_edge_eq]
  rw [eq]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases h : i≠j ∧ ({i,j}:Finset J)=e
  · have hh : MeasurableSet {x : J→S | (x i,x j)∈A} := by
      have m : Measurable (fun x : J→S => (x i,x j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      exact m am
    convert hh using 1
    ext x
    simp [h.1,h.2]
  · have eq : {x : J→S | i≠j ∧ (x i,x j)∈A ∧ ({i,j}:Finset J)=e}=∅ := by
      ext x
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      exact fun z => h ⟨z.1,z.2.2⟩
    rw [eq]
    exact MeasurableSet.empty

theorem measurable_sample_predicate_fiber (A : Set (S×S)) (am : MeasurableSet A) (G : EdgeGraph J) :
    MeasurableSet (fiberOf (samplePredicateGraph A) G) := by
  classical
  have e : fiberOf (samplePredicateGraph A) G =
    ⋂ e : Finset J, {x : J→S | e∈samplePredicateGraph A x ↔ e∈G} := by
    ext x
    rw [Set.mem_iInter]
    exact Finset.ext_iff
  rw [e]
  apply MeasurableSet.iInter
  intro e
  by_cases he : e∈G
  · simpa [he] using measurable_sample_predicate_edge A am e
  · have eq : {x : J→S | e∈samplePredicateGraph A x ↔ e∈G} =
        {x : J→S | e∈samplePredicateGraph A x}ᶜ := by
      ext x
      simp [he]
    rw [eq]
    exact (measurable_sample_predicate_edge A am e).compl

theorem measurable_sample_predicate (A : Set (S×S)) (am : MeasurableSet A) (P : EdgeGraph J→Prop) :
    MeasurableSet {x : J→S | P (samplePredicateGraph A x)} := by
  classical
  have e : {x : J→S | P (samplePredicateGraph A x)} =
    ⋃ g ∈ (Finset.univ.filter P : Finset (EdgeGraph J)),fiberOf (samplePredicateGraph A) g := by
    ext x
    simp only [mem_ofPred_eq,Set.mem_iUnion,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun h => ⟨samplePredicateGraph A x,h,rfl⟩,fun ⟨g,h,e⟩ => e.symm ▸ h⟩
  rw [e]
  exact MeasurableSet.biUnion (Finset.univ.filter P).countable_toSet (fun g _ =>
    measurable_sample_predicate_fiber A am g)

#print axioms measurable_sample_predicate
end RobustFolkman.GeometricGap
