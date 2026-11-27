import PairedIndependent
open Set MeasureTheory Function Filter
namespace SparseHalfGraphon
variable {X I : Type*} [MeasurableSpace X] [Countable I] [Nonempty I]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- A low paired capacity creates an independent outside set. Therefore an
independent-set cap supplies enough mass for the balanced allocation. -/
theorem paired_allocation_of_independence_cap
    (W : Kernel X) (S : Set X) (ms : MeasurableSet S) (P Q : I → Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inside : ∀ i, P i ∪ Q i ⊆ S)
    (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i => P i ∪ Q i))
    (support : ∀ᵐ z ∂μ.prod μ, z.1∈S → z.2∈S → 0<W.W z →
      ∃ i, (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i))
    (cap m : ℝ) (mn : 0≤m) (available : m≤2*(μ.real S-cap))
    (indCap : ∀ T : Set X, MeasurableSet T → T ⊆ S →
      (∀ᵐ z ∂μ.prod μ, z.1∈T → z.2∈T → W.W z=0) → μ.real T≤cap) :
    ∃ D : X → ℝ, BMeas D ∧ (∀ x, 0≤D x ∧ D x≤1) ∧ (∀ x∉S, D x=0) ∧
      (∫ x,D x ∂μ)=m ∧
      ∀ v, PairedRow μ W P Q v → load μ W D v=m/2 := by
  obtain ⟨T,tm,ti,tμ,tW⟩ := paired_independent_dual μ W S ms P Q mp mq inside outer support
  have H := indCap T tm ti tW
  rw [tμ] at H
  obtain ⟨D,dm,du,dz,_,dμ,dl⟩ := paired_fractional_allocation μ W P Q mp mq inner outer
    m mn (by linarith)
  exact ⟨D,dm,du,fun x hx => dz x (fun h => hx ((iUnion_subset inside) h)),dμ,dl⟩

#print axioms paired_allocation_of_independence_cap
end SparseHalfGraphon
