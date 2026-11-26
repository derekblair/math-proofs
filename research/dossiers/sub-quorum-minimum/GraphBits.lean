import Selectors
import Mathlib.Data.Sym.Card
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace QuorumMinimum

abbrev EdgeSlot (A : Type) := { z : Sym2 A // ¬z.IsDiag }

def edgeSlots {A B : Type} (u : A ↪ B) : EdgeSlot A ↪ EdgeSlot B where
  toFun z := ⟨z.val.map u, fun h => z.property ((Sym2.isDiag_map u.injective).mp h)⟩
  inj' := fun _ _ e => Subtype.ext (Sym2.map.injective u.injective (congrArg Subtype.val e))

noncomputable def bitGraph {A : Type} (p : EdgeSlot A → Bool) : SimpleGraph A :=
  .fromEdgeSet {e | ∃ h : ¬e.IsDiag, p ⟨e,h⟩ = true}

theorem bitGraph_adj {A : Type} (p : EdgeSlot A → Bool) {x y : A} (h : x ≠ y) :
    (bitGraph p).Adj x y ↔ p ⟨s(x,y),by simpa using h⟩ = true := by
  simp [bitGraph, SimpleGraph.fromEdgeSet_adj, h]

theorem bitGraph_flip {A : Type} (p : EdgeSlot A → Bool) :
    bitGraph (flip p) = (bitGraph p)ᶜ := by
  ext x y
  by_cases h : x=y
  · subst y; simp
  · rw [SimpleGraph.compl_adj,bitGraph_adj _ h,bitGraph_adj _ h]
    simp [h,flip]

theorem slot_count (L : Nat) :
    Fintype.card (EdgeSlot (Fin (32*L+1))) = 8*(2*L*(32*L+1)) := by
  rw [Sym2.card_subtype_not_diag, Fintype.card_fin, Nat.choose_two_right]
  have h : (32*L+1)-1=32*L := by omega
  rw [h]
  have h' : (32*L+1)*(32*L) = 2*(8*(2*L*(32*L+1))) := by ring
  rw [h']
  omega

/-- Common witness for every labeled embedding of a test subset, for both signs. -/
theorem test_set_bits (n L : Nat) (lpos : 0<L) (nlim : n≤2^L) :
    let t := 32*L+1
    let r := 2*L*t
    ∃ p : EdgeSlot (Fin n) → Bool,
      ∀ u : Fin t ↪ Fin n,
        let v := ((Fintype.equivFinOfCardEq (slot_count L)).symm.toEmbedding).trans (edgeSlots u)
        zeros (p ∘ v) < 6*r ∧ zeros ((flip p) ∘ v) < 6*r := by
  classical
  let t := 32*L+1
  let r := 2*L*t
  let v (u : Fin t ↪ Fin n) : Fin (8*r) ↪ EdgeSlot (Fin n) :=
    ((Fintype.equivFinOfCardEq (slot_count L)).symm.toEmbedding).trans (edgeSlots u)
  have bnd : Fintype.card (Fin t ↪ Fin n) ≤ 2^(L*t) := by
    have b := Fintype.card_le_of_injective (fun u : Fin t ↪ Fin n => (u : Fin t → Fin n))
      (fun u w eq => Function.Embedding.ext fun i => congrFun eq i)
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at b
    exact b.trans (by rw [pow_mul]; exact Nat.pow_le_pow_left nlim t)
  have p2 : 2≤L*t := by
    have h : 2≤t := by dsimp [t]; omega
    exact h.trans (by simpa using Nat.mul_le_mul_right t lpos)
  have gap : L*t+1<r := by
    dsimp [r]; rw [Nat.mul_assoc]; omega
  obtain ⟨p,h⟩ := exists_balanced r (L*t) v bnd gap
  refine ⟨p,fun u => ⟨?_,?_⟩⟩
  · exact Nat.lt_of_not_ge (fun h' => (h u).1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h'⟩))
  · exact Nat.lt_of_not_ge (fun h' => (h u).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h'⟩))

#print axioms bitGraph_flip
#print axioms test_set_bits

end QuorumMinimum
