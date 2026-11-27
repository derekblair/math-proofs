import PairedCapacity
open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {X I : Type*} [MeasurableSpace X] [Countable I]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- If every supported edge in an outside set crosses the two sides of a
matching pair, keep the larger side of every pair and every leftover point. -/
theorem paired_independent_dual
    (W : Kernel X) (S : Set X) (ms : MeasurableSet S) (P Q : I → Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inside : ∀ i, P i ∪ Q i ⊆ S)
    (outer : Pairwise (Disjoint on fun i => P i ∪ Q i))
    (support : ∀ᵐ z ∂μ.prod μ, z.1∈S → z.2∈S → 0<W.W z →
      ∃ i, (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i)) :
    ∃ T : Set X, MeasurableSet T ∧ T ⊆ S ∧
       μ.real T = μ.real S - ∑' i, cellCapacity μ P Q i ∧
       ∀ᵐ z ∂μ.prod μ, z.1∈T → z.2∈T → W.W z=0 := by
  classical
  let D (i : I) := if μ.real (P i)≤μ.real (Q i) then P i else Q i
  have dm (i) : MeasurableSet (D i) := by
    by_cases H : μ.real (P i)≤μ.real (Q i) <;> simp [D,H,mp,mq]
  have DS (i) : D i ⊆ P i ∪ Q i := by
    by_cases H : μ.real (P i)≤μ.real (Q i)
    · simpa only [D,if_pos H] using (subset_union_left : P i ⊆ P i ∪ Q i)
    · simpa only [D,if_neg H] using (subset_union_right : Q i ⊆ P i ∪ Q i)
  have dd : Pairwise (Disjoint on D) := fun i j ne => (outer ne).mono (DS i) (DS j)
  have massD (i) : μ.real (D i)=cellCapacity μ P Q i := by
    by_cases H : μ.real (P i)≤μ.real (Q i)
    · simp [D,H,cellCapacity,min_eq_left H]
    · simp [D,H,cellCapacity,min_eq_right (le_of_not_ge H)]
  let U := ⋃ i, D i
  have mu : MeasurableSet U := MeasurableSet.iUnion dm
  have us : U⊆S := iUnion_subset fun i => (DS i).trans (inside i)
  let T := S \ U
  refine ⟨T,ms.diff mu,sdiff_subset,?_,?_⟩
  · show μ.real (S \ U)=_
    rw [measureReal_sdiff us mu,← (real_mass_hasSum μ D dm dd).tsum_eq]
    simp_rw [massD]
  · filter_upwards [support] with z hz hz1 hz2
    apply le_antisymm _ (W.nonneg z)
    by_contra! h
    obtain ⟨i,he⟩ := hz hz1.1 hz2.1 h
    have DS' : ∀ x∈D i, x∈U := fun x hx => mem_iUnion.mpr ⟨i,hx⟩
    by_cases H : μ.real (P i)≤μ.real (Q i)
    · have d : D i=P i := if_pos H
      rcases he with ⟨p,q⟩|⟨q,p⟩
      · exact hz1.2 (DS' z.1 (d.symm ▸ p))
      · exact hz2.2 (DS' z.2 (d.symm ▸ p))
    · have d : D i=Q i := if_neg H
      rcases he with ⟨p,q⟩|⟨q,p⟩
      · exact hz2.2 (DS' z.2 (d.symm ▸ q))
      · exact hz1.2 (DS' z.1 (d.symm ▸ q))

#print axioms paired_independent_dual
end SparseHalfGraphon
