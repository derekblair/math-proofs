import OutsideGreedyHalf

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon
open SparseHalfCountableEndpoint

variable {X I : Type*} [MeasurableSpace X] [Countable I]
variable (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def larger10 (P Q : I→Set X) (i : I) : ℝ :=
  10*max (μ.real (P i)) (μ.real (Q i))
noncomputable def smaller10 (P Q : I→Set X) (i : I) : ℝ :=
  10*min (μ.real (P i)) (μ.real (Q i))

/-- A global product restricted to the outside sees exactly its own two
restricted marginals; unfold the rectangle to obtain a conditional AE edge. -/
theorem outside_prod_restrict_edge (K : Kernel X) (S : Set X) (ms : MeasurableSet S)
    (P Q : I→Set X)
    (edge : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict S), 0<K.W z →
      ∃ i, (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i)) :
    ∀ᵐ z ∂μ.prod μ, z.1∈S → z.2∈S → 0<K.W z →
      ∃ i, (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i) := by
  rw [Measure.prod_restrict] at edge
  have a := (ae_restrict_iff' (ms.prod ms)).mp edge
  filter_upwards [a] with z hz hs ht pos
  exact hz ⟨hs,ht⟩ pos

/-- The actual outside-only Half is defined for either labeling of each
active pair; orient the capacities internally by their masses. -/
theorem outside_greedy_half (K : Kernel X) (S : Set X) (ms : MeasurableSet S) (P Q : I→Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inside : ∀ i, P i∪Q i⊆S) (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i=>P i∪Q i))
    (edge : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict S), 0<K.W z →
      ∃ i, (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i))
    (cap : ∀ i, μ.real (P i)≤1/5 ∧ μ.real (Q i)≤1/5)
    (size : μ.real S=3/5) :
    (5 ≤ isolate10 μ S P Q+(∑' i, larger10 μ P Q i) ∧
      ∃ H : Half μ,(∀ x∉S,H.f x=0) ∧ halfEnergy μ K H≤0) ∨
    ∃ θ : ℝ, 0≤θ ∧ θ≤2 ∧
      ∃ H : Half μ,(∀ x∉S,H.f x=0) ∧
        halfEnergy μ K H≤dual (larger10 μ P Q) (smaller10 μ P Q) θ /100 := by
  let c (i : I) := μ.real (Q i)≤μ.real (P i)
  let L (i : I) := if c i then P i else Q i
  let M (i : I) := if c i then Q i else P i
  have lm (i) : MeasurableSet (L i) := by by_cases h:c i <;> simp [L,h,mp,mq]
  have mm (i) : MeasurableSet (M i) := by by_cases h:c i <;> simp [M,h,mp,mq]
  have ci (i) : L i∪M i=P i∪Q i := by by_cases h:c i <;> simp [L,M,h,union_comm]
  have d (i) : Disjoint (L i) (M i) := by
    by_cases h:c i
    · simpa [L,M,h] using inner i
    · simpa [L,M,h] using (inner i).symm
  have ct (i) : μ.real (M i)≤μ.real (L i) := by
    by_cases h:c i
    · simpa only [L,M,if_pos h] using h
    · have e : μ.real (P i)≤μ.real (Q i) := le_of_lt (lt_of_not_ge h)
      simpa [L,M,h] using e
  have cl (i) : μ.real (L i)≤1/5 := by
    by_cases h:c i
    · simpa [L,h] using (cap i).1
    · simpa [L,h] using (cap i).2
  have ce : ∀ᵐ z ∂μ.prod μ, z.1∈S → z.2∈S → 0<K.W z →
      ∃ i, (z.1∈L i ∧ z.2∈M i) ∨ (z.1∈M i ∧ z.2∈L i) := by
    filter_upwards [outside_prod_restrict_edge μ K S ms P Q edge] with z hz hs ht pos
    obtain ⟨i,a⟩ := hz hs ht pos
    refine ⟨i,?_⟩
    by_cases h:c i
    · simpa [L,M,h] using a
    · simpa [L,M,h,or_comm] using a
  have a : side10 μ L=larger10 μ P Q := by
    funext i
    by_cases h:c i
    · simp only [side10,larger10,L,if_pos h,max_eq_left h]
    · simp only [side10,larger10,L,if_neg h,max_eq_right (le_of_lt (lt_of_not_ge h))]
  have b : side10 μ M=smaller10 μ P Q := by
    funext i
    by_cases h:c i
    · simp only [side10,smaller10,M,if_pos h,min_eq_right h]
    · simp only [side10,smaller10,M,if_neg h,min_eq_left (le_of_lt (lt_of_not_ge h))]
  have iso : isolate10 μ S L M=isolate10 μ S P Q := by simp only [isolate10,ci]
  have H := outside_greedy_half_oriented μ K S ms L M lm mm
    (fun i=>ci i ▸ inside i) d (by simpa only [Function.onFun,ci] using outer) ce ct cl size
  rwa [a,b,iso] at H

theorem outside_dual_ge_two_maxmin (K : Kernel X) (S : Set X) (ms : MeasurableSet S) (P Q : I→Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inside : ∀ i, P i∪Q i⊆S) (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i=>P i∪Q i))
    (edge : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict S), 0<K.W z →
      ∃ i, (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i))
    (cap : ∀ i, μ.real (P i)≤1/5 ∧ μ.real (Q i)≤1/5)
    (size : μ.real S=3/5) (high : 1/50≤beta μ K) :
    ∃ θ : ℝ, 0≤θ ∧ θ≤2 ∧ 2≤dual (larger10 μ P Q) (smaller10 μ P Q) θ := by
  have cost_ge (H : Half μ) : 1/50≤halfEnergy μ K H :=
    high.trans (csInf_le (range_bdd μ K) ⟨H,rfl⟩)
  rcases outside_greedy_half μ K S ms P Q mp mq inside inner outer edge cap size
    with ⟨_,H,_,z⟩|⟨θ,θ0,θ2,H,_,h⟩
  · linarith [cost_ge H]
  · exact ⟨θ,θ0,θ2,by linarith [cost_ge H]⟩

/-- Exact total mass and summability for the normalized larger/smaller bank. -/
theorem paired_bank_measure (S : Set X) (P Q : I→Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inside : ∀ i, P i∪Q i⊆S) (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i=>P i∪Q i)) :
    Summable (fun i => larger10 μ P Q i + smaller10 μ P Q i) ∧
      (∑' i, (larger10 μ P Q i + smaller10 μ P Q i))+isolate10 μ S P Q = 10*μ.real S := by
  let U := ⋃ i,P i∪Q i
  have um : MeasurableSet U := MeasurableSet.iUnion (fun i=>(mp i).union (mq i))
  have us : U⊆S := iUnion_subset inside
  have E (i : I) : larger10 μ P Q i + smaller10 μ P Q i=10*μ.real (P i∪Q i) := by
    rw [larger10,smaller10,←mul_add,max_add_min,measureReal_union (inner i) (mq i)]
  have sum := real_mass_hasSum μ (fun i=>P i∪Q i) (fun i=>(mp i).union (mq i)) outer
  refine ⟨?_,?_⟩
  · simp_rw [E]
    exact sum.summable.mul_left 10
  · simp_rw [E]
    rw [sum.summable.tsum_mul_left,sum.tsum_eq,isolate10,measureReal_sdiff us um]
    ring

#print axioms outside_greedy_half
#print axioms outside_dual_ge_two_maxmin
end SparseHalfGraphon
