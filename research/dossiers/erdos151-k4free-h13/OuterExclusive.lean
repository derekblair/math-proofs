import HubDomains

namespace Erdos151H13
open Erdős151 Erdos151H12 Erdos151Ramsey

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

noncomputable def exclusiveCoreSide (x w y : V) : Finset V :=
  outerCoreSide G C x w \ neighbors G y

theorem exclusive_core_side_size
    (sub : ∀ a b, C a b → G a b) (x w y : V) :
    (neighbors C x).card ≤ (exclusiveCoreSide G C x w y).card +
      (neighbors G x ∩ neighbors G w).card +
      ((neighbors G x ∩ neighbors G y) \ insert w (neighbors G w)).card + 1 := by
  let A := outerCoreSide G C x w
  let S := (neighbors G x ∩ neighbors G y) \ insert w (neighbors G w)
  have h := Finset.card_sdiff_add_card_inter A (neighbors G y)
  change (exclusiveCoreSide G C x w y).card + _ = A.card at h
  have hs : A ∩ neighbors G y ⊆ S := by
    intro a ha
    obtain ⟨aA,aY⟩ := Finset.mem_inter.mp ha
    obtain ⟨aC,no⟩ := Finset.mem_sdiff.mp aA
    have gx := sub x a ((mem_neighbors C).mp aC)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr gx,aY⟩,no⟩
  have g := Finset.card_le_card hs
  have b := outer_core_side_size G C sub x w
  change _ ≤ A.card + (neighbors G x ∩ neighbors G w).card + 1 at b
  change _ ≤ _ + S.card + 1
  omega

theorem exclusive_core_side_mem
    (sub : ∀ a b, C a b → G a b)
    (coreNonlone : ∀ a b, C a b → ¬ Lone G a b) (x w y : V) :
    ∀ a ∈ exclusiveCoreSide G C x w y,
      a ∈ outerCandidates G x w y ∧ G x a ∧ ¬ G y a := by
  classical
  intro a ha
  obtain ⟨aA,nY⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨aC,no⟩ := Finset.mem_sdiff.mp aA
  have hx := (mem_neighbors C).mp aC
  have gx := sub x a hx
  have gy : ¬ G y a := fun h => nY ((mem_neighbors G).mpr h)
  refine ⟨?_,gx,gy⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_left _ ((mem_neighbors G).mpr gx),no⟩,
    coreNonlone x a hx,fun h => gy h.1⟩

/-- Independent sets from the two exclusive sides can be kept together;
any ambient cross edge belongs to neither outer-hub conflict link. -/
theorem independent_exclusive_union
    (x y : V) (A B : Finset V)
    (Ax : ∀ a ∈ A, G x a ∧ ¬ G y a) (By : ∀ a ∈ B, G y a ∧ ¬ G x a)
    (hA : Independent G A) (hB : Independent G B) :
    Disjoint A B ∧ Independent (pairConflict G x y) (A ∪ B) := by
  constructor
  · exact Finset.disjoint_left.mpr (fun a ha hb => (By a hb).2 (Ax a ha).1)
  · intro a ha b hb e
    rcases Finset.mem_union.mp ha with al|ar <;>
      rcases Finset.mem_union.mp hb with bl|br
    · exact hA _ al _ bl e.1
    · rcases e.2 with h|h
      · exact (By _ br).2 h.2
      · exact (Ax _ al).2 h.1
    · rcases e.2 with h|h
      · exact (By _ ar).2 h.1
      · exact (Ax _ bl).2 h.2
    · exact hB _ ar _ br e.1

#print axioms exclusive_core_side_size
#print axioms exclusive_core_side_mem
#print axioms independent_exclusive_union
end Erdos151H13
