import N63HostAdj
import Mathlib.Data.Fin.Tuple.Sort
namespace Erdos151N63
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V → V → Prop) [DecidableRel G]
/-- Every nine- or ten-vertex link of directed degree sum exceeding
three times its size has a maximum pivot with at most n−5
nonneighbors. This is the starting point of the finite normalization. -/
theorem max_normalization_of_high (n : Nat) (hn : Fintype.card V = n)
    (hd : ∃ v : V, 4≤fullDeg G v)
    (irr : ∀ v, ¬ G v v) :
    ∃ w : V, 4 ≤ fullDeg G w ∧ fullDeg G w+1 ≤ n ∧
      (∀ v : V, fullDeg G v ≤ fullDeg G w) ∧
      Fintype.card {z : V // z ≠ w ∧ ¬G w z} = n-1-fullDeg G w := by
  classical
  have he : Finset.univ.Nonempty (α := V) := by
    by_contra! h
    have hz : (Finset.univ : Finset V) = ∅ := h
    obtain ⟨v,_⟩ := hd
    exact (Finset.notMem_empty v) (hz ▸ Finset.mem_univ v)
  obtain ⟨w,hw,hmax⟩ := Finset.exists_max_image Finset.univ (fullDeg G) he
  have hmax' : ∀ v : V, fullDeg G v ≤ fullDeg G w :=
    fun v => hmax v (Finset.mem_univ _)
  obtain ⟨v,hv⟩ := hd
  have h4 : 4 ≤ fullDeg G w := hv.trans (hmax' v)
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

#print axioms max_normalization_of_high

/-- Bipartition of a normalized link around a maximum-degree vertex:
the left block is independent, the right block and mixed entries
are the only ones not specified by the pivot. -/
theorem max_normalization_blocks_of_high (n : Nat) (hn : Fintype.card V = n)
    (hd : ∃ v : V, 4≤fullDeg G v)
    (irr : ∀ v, ¬ G v v)
    (tf : ∀ w x y, G w x → G w y → ¬G x y) :
    ∃ w : V, 4 ≤ fullDeg G w ∧ fullDeg G w+1 ≤ n ∧
      (∀ v : V, fullDeg G v ≤ fullDeg G w) ∧
      ∃ L : Fin (fullDeg G w) ≃ {z : V // G w z},
      ∃ R : Fin (n-1-fullDeg G w) ≃ {z : V // z ≠ w ∧ ¬G w z},
        (∀ i j, ¬G (L i).val (L j).val) ∧
        ∀ z : V, z = w ∨ (∃ i, (L i).val = z) ∨ (∃ j, (R j).val = z) := by
  classical
  obtain ⟨w,h4,hwn,hm,hr⟩ := max_normalization_of_high G n hn hd irr
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

#print axioms max_normalization_blocks_of_high
/-- The row masks can be sorted without altering any graph edge: permute
only the independent neighbor block of the chosen pivot. -/
theorem max_normalization_sorted_of_high (n : Nat) (hn : Fintype.card V = n)
    (hd : ∃ v : V, 4≤fullDeg G v)
    (irr : ∀ v, ¬ G v v)
    (tf : ∀ w x y, G w x → G w y → ¬G x y) :
    ∃ w : V, 4 ≤ fullDeg G w ∧ fullDeg G w+1 ≤ n ∧
      (∀ v : V, fullDeg G v ≤ fullDeg G w) ∧
      ∃ L : Fin (fullDeg G w) ≃ {z : V // G w z},
      ∃ R : Fin (n-1-fullDeg G w) ≃ {z : V // z ≠ w ∧ ¬G w z},
      ∃ M : Fin (fullDeg G w) → Nat,
        Monotone M ∧ (∀ i, M i < 2^(n-1-fullDeg G w)) ∧
        (∀ i j, (M i).testBit j.val = true ↔ G (L i).val (R j).val) ∧
        (∀ i j, ¬G (L i).val (L j).val) ∧
        ∀ z : V, z = w ∨ (∃ i, (L i).val = z) ∨ (∃ j, (R j).val = z) := by
  obtain ⟨w,h4,hwn,hm,L,R,hL,cover⟩ := max_normalization_blocks_of_high G n hn hd irr tf
  let q := n-1-fullDeg G w
  let B (i : Fin (fullDeg G w)) := bitsOf q (fun j => decide (G (L i).val (R j).val))
  let M (i : Fin (fullDeg G w)) := (B i).toNat
  let σ := Tuple.sort M
  refine ⟨w,h4,hwn,hm,σ.trans L,R,M ∘ σ, Tuple.monotone_sort M,?_,?_,?_,?_⟩
  · intro i
    exact (B (σ i)).isLt
  · intro i j
    change (B (σ i)).toNat.testBit j.val = true ↔ G (L (σ i)).val (R j).val
    rw [bitsOf_reads]
    simp
  · intro i j
    exact hL (σ i) (σ j)
  · intro z
    rcases cover z with h|⟨i,hi⟩|h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨σ.symm i,by simpa using hi⟩)
    · exact Or.inr (Or.inr h)


#print axioms max_normalization_sorted_of_high
end Erdos151N63
