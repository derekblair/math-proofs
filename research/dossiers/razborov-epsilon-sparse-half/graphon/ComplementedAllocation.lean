import PairedProfileCells
open Set MeasureTheory Function Filter
namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
variable (ω ν : Measure X) [IsFiniteMeasure ω] [IsFiniteMeasure ν]

/-- Complementary anchor profiles of almost all outside edges, together with
an outside independent-set cap, force balanced fractional mass on the outside. -/
theorem complemented_allocation_of_independence_cap
    (K : Kernel X) (nonnull : ν univ ≠ 0) (S : Set X) (ms : MeasurableSet S)
    (h : ∀ᵐ z ∂ω.prod ω, K.W z=0 ∨ ∀ᵐ v ∂ν, ComplementaryAt K z.1 z.2 v)
    (cap m : ℝ) (mn : 0≤m) (available : m≤2*(ω.real S-cap))
    (indCap : ∀ T : Set X, MeasurableSet T → T⊆S →
      (∀ᵐ z ∂ω.prod ω, z.1∈T → z.2∈T → K.W z=0) → ω.real T≤cap) :
    ∃ D : X → ℝ, BMeas D ∧ (∀ x, 0≤D x ∧ D x≤1) ∧ (∀ x∉S, D x=0) ∧
      (∫ x,D x ∂ω)=m ∧ (∀ᵐ v ∂ν, load ω K D v=m/2) := by
  obtain ⟨T,tm,tg,tp,tu⟩ := countable_generating_pi (X:=X)
  obtain ⟨I,ic,inon,P,Q,mp,mq,inside,inner,outer,edge,row⟩ :=
    paired_profile_cells ω ν K T tm tg tp tu nonnull S ms h
  letI : Countable I := ic
  letI : Nonempty I := inon
  obtain ⟨D,dm,unit,off,dMass,dLoad⟩ :=
    paired_allocation_of_independence_cap ω K S ms P Q mp mq inside inner outer edge
      cap m mn available indCap
  exact ⟨D,dm,unit,off,dMass,by filter_upwards [row] with v hv using dLoad v hv⟩

#print axioms complemented_allocation_of_independence_cap
end SparseHalfGraphon

namespace SparseHalfGraphon
open Set MeasureTheory Function Filter
variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
variable (μ ω ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ω] [IsFiniteMeasure ν]

/-- Saturation and triangle-freeness supply the complementary profiles, so the
actual kernel yields an anchor-balanced fractional outside allocation. -/
theorem saturated_allocation_of_independence_cap
    (hν : ν ≪ μ) (hω : ω ≪ μ) (K : Kernel X)
    (nonnull : ν univ ≠ 0) (S : Set X) (ms : MeasurableSet S)
    (tri : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z=0)
    (rows : ∀ᵐ x ∂ω, mass ν/2≤deg ν K x)
    (cap m : ℝ) (mn : 0≤m) (available : m≤2*(ω.real S-cap))
    (indCap : ∀ T : Set X, MeasurableSet T → T⊆S →
      (∀ᵐ z ∂ω.prod ω, z.1∈T → z.2∈T → K.W z=0) → ω.real T≤cap) :
    ∃ D : X → ℝ, BMeas D ∧ (∀ x, 0≤D x ∧ D x≤1) ∧ (∀ x∉S, D x=0) ∧
      (∫ x,D x ∂ω)=m ∧ (∀ᵐ v ∂ν, load ω K D v=m/2) :=
  complemented_allocation_of_independence_cap ω ν K nonnull S ms
    (edge_complement μ ν ω hν hω K tri rows) cap m mn available indCap

#print axioms saturated_allocation_of_independence_cap
end SparseHalfGraphon
