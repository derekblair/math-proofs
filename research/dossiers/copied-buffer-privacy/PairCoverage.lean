import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace PairCoverage

open scoped BigOperators
variable {I X : Type*} [DecidableEq I] [DecidableEq X]

/-- A collection of width-two buffers covers two coordinates per read
exactly when the selected buffers are pairwise disjoint. -/
theorem full_pair_coverage (S : Finset I) (p : I → Finset X)
    (size : ∀ i, (p i).card = 2) :
    (S.biUnion p).card = 2*S.card ↔ (S : Set I).PairwiseDisjoint p := by
  constructor
  · intro h
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S ni ih =>
      rw [Finset.biUnion_insert, Finset.card_insert_of_notMem ni] at h
      have bound : (S.biUnion p).card ≤ 2*S.card := by
        calc
          _ ≤ ∑ j ∈ S, (p j).card := Finset.card_biUnion_le
          _ = _ := by simp [size, Nat.mul_comm]
      have hu := Finset.card_union_add_card_inter (p i) (S.biUnion p)
      have hi := size i
      have dis : Disjoint (p i) (S.biUnion p) := by
        apply Finset.disjoint_iff_inter_eq_empty.mpr
        apply Finset.card_eq_zero.mp
        omega
      have exactCard : (S.biUnion p).card = 2*S.card := by omega
      have prior := ih exactCard
      intro a ha b hb ne
      change a ∈ insert i S at ha
      change b ∈ insert i S at hb
      rcases Finset.mem_insert.mp ha with rfl | haS
      · have hb' := (Finset.mem_insert.mp hb).resolve_left ne.symm
        exact dis.mono_right (fun x hx => Finset.mem_biUnion.mpr ⟨b,hb',hx⟩)
      · rcases Finset.mem_insert.mp hb with rfl | hbS
        · have included : p a ⊆ S.biUnion p := by
            intro x hx
            exact Finset.mem_biUnion.mpr ⟨a,haS,hx⟩
          exact (dis.mono_right included).symm
        · exact prior haS hbS ne
  · intro h
    rw [Finset.card_biUnion h]
    simp [size, Nat.mul_comm]

#print axioms full_pair_coverage
end PairCoverage
