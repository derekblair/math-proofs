import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

namespace Erdos151N63
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V → V → Prop) [DecidableRel G]

def fullDeg (v : V) : Nat := (Finset.univ.filter (G v)).card

/-- Every nine- or ten-vertex link of directed degree sum exceeding
three times its size has a maximum pivot with at most n−5
nonneighbors. This is the starting point of the finite normalization. -/
theorem max_normalization (n : Nat) (hn : Fintype.card V = n)
    (hd : 3*n < ∑ v : V, fullDeg G v)
    (irr : ∀ v, ¬ G v v) :
    ∃ w : V, 4 ≤ fullDeg G w ∧ fullDeg G w+1 ≤ n ∧
      (∀ v : V, fullDeg G v ≤ fullDeg G w) ∧
      Fintype.card {z : V // z ≠ w ∧ ¬G w z} = n-1-fullDeg G w := by
  classical
  have he : Finset.univ.Nonempty (α := V) := by
    by_contra! h
    have hz : (Finset.univ : Finset V) = ∅ := h
    rw [hz,Finset.sum_empty] at hd
    omega
  obtain ⟨w,hw,hmax⟩ := Finset.exists_max_image Finset.univ (fullDeg G) he
  have hmax' : ∀ v : V, fullDeg G v ≤ fullDeg G w :=
    fun v => hmax v (Finset.mem_univ _)
  have h4 : 4 ≤ fullDeg G w := by
    by_contra! h
    have hr : (∑ v : V, fullDeg G v) ≤ ∑ _v : V, (3:Nat) :=
      Finset.sum_le_sum fun v _ => (hmax' v).trans (by omega)
    have hh : (∑ v : V, fullDeg G v) ≤ 3*n := by simpa [hn,Nat.mul_comm] using hr
    omega
  let S := Finset.univ.filter (G w)
  let U := (Finset.univ : Finset V) \ insert w S
  have hwS : w ∉ S := by simpa [S] using irr w
  have hi := Finset.card_le_card (Finset.subset_univ (insert w S))
  rw [Finset.card_insert_of_notMem hwS,Finset.card_univ,hn] at hi
  have hUc : U.card = n-1-S.card := by
    rw [show U = (Finset.univ : Finset V) \ insert w S from rfl,
        Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_insert_of_notMem hwS, Finset.card_univ,hn]
    omega
  have hEq : U = Finset.univ.filter (fun z => z ≠ w ∧ ¬ G w z) := by
    ext z
    simp [U,S,not_or]
  refine ⟨w,h4,hi,hmax',?_⟩
  simpa [fullDeg,S] using (show Fintype.card {z : V // z ≠ w ∧ ¬G w z} = n-1-S.card from by rw [Fintype.card_subtype, ← hEq, hUc])

#print axioms max_normalization

/-- Bipartition of a normalized link around a maximum-degree vertex:
the left block is independent, the right block and mixed entries
are the only ones not specified by the pivot. -/
theorem max_normalization_blocks (n : Nat) (hn : Fintype.card V = n)
    (hd : 3*n < ∑ v : V, fullDeg G v)
    (irr : ∀ v, ¬ G v v)
    (tf : ∀ w x y, G w x → G w y → ¬G x y) :
    ∃ w : V, 4 ≤ fullDeg G w ∧ fullDeg G w+1 ≤ n ∧
      (∀ v : V, fullDeg G v ≤ fullDeg G w) ∧
      ∃ L : Fin (fullDeg G w) ≃ {z : V // G w z},
      ∃ R : Fin (n-1-fullDeg G w) ≃ {z : V // z ≠ w ∧ ¬G w z},
        (∀ i j, ¬G (L i).val (L j).val) ∧
        ∀ z : V, z = w ∨ (∃ i, (L i).val = z) ∨ (∃ j, (R j).val = z) := by
  classical
  obtain ⟨w,h4,hwn,hm,hr⟩ := max_normalization G n hn hd irr
  have hl : Fintype.card {z : V // G w z} = fullDeg G w := Fintype.card_subtype _
  let L := (Fintype.equivFinOfCardEq hl).symm
  let R := (Fintype.equivFinOfCardEq hr).symm
  refine ⟨w,h4,hwn,hm,L,R,fun i j => tf w _ _ (L i).property (L j).property,?_⟩
  intro z
  by_cases hz : z = w
  · exact Or.inl hz
  by_cases hzw : G w z
  · obtain ⟨i,hi⟩ := L.surjective ⟨z,hzw⟩
    exact Or.inr (Or.inl ⟨i,congrArg Subtype.val hi⟩)
  · obtain ⟨j,hj⟩ := R.surjective ⟨z,hz,hzw⟩
    exact Or.inr (Or.inr ⟨j,congrArg Subtype.val hj⟩)

#print axioms max_normalization_blocks
end Erdos151N63
