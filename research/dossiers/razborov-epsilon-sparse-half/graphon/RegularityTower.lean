import FiniteWeakRegularity

open MeasureTheory Set
namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- Countable tower of nested weak approximations; cardinalities have a
deterministic recurrence independent of the kernel or underlying space. -/
theorem regularity_tower (K : Kernel X) (hμ : mass μ=1)
    (eps : ℕ→ℝ) (fuel : ℕ→ℕ) (he : ∀ n, 0<eps n)
    (hf : ∀ n, 1<((fuel n:ℝ)+1)*(eps n)^2) (P : ColorPartition X) :
    ∃ Q : ℕ→ColorPartition X, Q 0=P ∧
      ∀ n, refines (Q n) (Q (n+1)) ∧
        (Q (n+1)).size≤(Q n).size*4^(fuel n) ∧
        CutBound μ K (partitionKernel μ K (Q (n+1))) (eps n) := by
  classical
  let next : ℕ→ColorPartition X→ColorPartition X := fun n P' =>
    Classical.choose (finite_weak_regular μ K hμ (eps n) (he n) (fuel n) (hf n) P')
  let Q : ℕ → ColorPartition X := Nat.rec P (fun n P' => next n P')
  refine ⟨Q,rfl,?_⟩
  intro n
  change refines (Q n) (next n (Q n)) ∧
    (next n (Q n)).size≤(Q n).size*4^(fuel n) ∧
    CutBound μ K (partitionKernel μ K (next n (Q n))) (eps n)
  exact Classical.choose_spec (finite_weak_regular μ K hμ (eps n) (he n) (fuel n) (hf n) (Q n))

/-- The exact squared L² gap of two nested block kernels equals the
difference of their energies, giving Cauchy control for a regularity tower. -/
theorem partition_energy_difference (K : Kernel X) (P Q : ColorPartition X)
    (hr : refines P Q) :
    blockEnergy μ (partitionKernel μ K Q)-blockEnergy μ (partitionKernel μ K P) =
      ∫ z, ((partitionKernel μ K Q).W z-(partitionKernel μ K P).W z)^2 ∂μ.prod μ := by
  obtain ⟨p,hp⟩ := hr
  let pp : Fin Q.size×Fin Q.size→Fin P.size×Fin P.size := fun z => (p z.1,p z.2)
  have he (z : X×X) : pairLabel P.label z=pp (pairLabel Q.label z) := by
    change (P.label z.1,P.label z.2)=(p (Q.label z.1),p (Q.label z.2))
    rw [hp z.1,hp z.2]
  exact refinement_energy (μ.prod μ)
    (pairLabel P.label) (pairLabel Q.label) pp
    (pair_label_meas P.label P.measurable_label) (pair_label_meas Q.label Q.measurable_label)
    he K.W (BMeas.of_unit K.measurable_W K.nonneg K.le_one)

#print axioms regularity_tower
#print axioms partition_energy_difference
end SparseHalfGraphon
