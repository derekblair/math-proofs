import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Set Topology Function
namespace SparseHalfGraphon

/-- Diagonal subsequence for countably many compact, metrizable
coordinates. Coordinates may independently be real intervals or
finite discrete parent maps. -/
theorem table_diagonal {I : Type*} [Countable I] {A : I→Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)]
    [∀ i, TopologicalSpace.MetrizableSpace (A i)] (f : ℕ→∀ i, A i) :
    ∃ q : ℕ→ℕ, ∃ g : ∀ i, A i, StrictMono q ∧
      ∀ i, Tendsto (fun n => f (q n) i) atTop (𝓝 (g i)) := by
  obtain ⟨g,q,hq,ht⟩ := CompactSpace.tendsto_subseq f
  exact ⟨q,g,hq,tendsto_pi_nhds.mp ht⟩

/-- Specialized unit-interval table extraction for all cell masses and
joint block integrals of a marked partition sequence. -/
theorem interval_table_diagonal {I : Type*} [Countable I]
    (f : ℕ→I→ℝ) (h₀ : ∀ n i, 0≤f n i) (h₁ : ∀ n i, f n i≤1) :
    ∃ q : ℕ→ℕ, ∃ g:I→ℝ, StrictMono q ∧
      (∀ i, 0≤g i ∧ g i≤1) ∧
      ∀ i, Tendsto (fun n => f (q n) i) atTop (𝓝 (g i)) := by
  let U := Set.Icc (0:ℝ) 1
  have : CompactSpace U := isCompact_iff_compactSpace.mp isCompact_Icc
  let F : ℕ→I→U := fun n i => ⟨f n i,h₀ n i,h₁ n i⟩
  obtain ⟨q,g,hq,ht⟩ := table_diagonal F
  refine ⟨q,fun i=>g i,hq,fun i => (g i).property,?_⟩
  intro i
  exact continuous_subtype_val.continuousAt.tendsto.comp (ht i)

#print axioms table_diagonal
#print axioms interval_table_diagonal
end SparseHalfGraphon
