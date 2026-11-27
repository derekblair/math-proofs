import ColorCore
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max

namespace IU

theorem clique_cap_index {k m n p q : Nat} {F : Finset Nat}
    (colors : Fin k → List Nat) (miss : Finset (Fin k))
    (count : k - miss.card ≤ m)
    (proper : ∀ i : Fin k, (colors i).Pairwise (fun a b => edge n p q a b = false))
    (cover : ∀ a∈F, ∃ i ∉ miss, a ∈ colors i)
    (edges : ∀ a∈F, ∀ b∈F, a≠b → edge n p q a b = true) :
    F.card ≤ m := by
  classical
  let I := Finset.univ \ miss
  let P := I.toList.map colors
  have ip : ∀ i : Fin k, i∈I ↔ i∉miss := by simp [I]
  have pl : P.length = k - miss.card := by
    simp [P,I, Finset.card_sdiff_of_subset (Finset.subset_univ miss),Fintype.card_fin]
  have cp : F.card ≤ P.length := by
    apply clique_cap n p q P
    · intro C hC
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hC
      exact proper i
    · intro a ha
      obtain ⟨i, hi, hac⟩ := cover a ha
      exact List.mem_flatten.mpr ⟨colors i,List.mem_map.mpr ⟨i,by simpa using (ip i).mpr hi,rfl⟩,hac⟩
    · exact edges
  omega

/-- A cap certificate for an ordered elimination down to a residual set.
    Larger stamps survive longer. Only colors absent from the surviving
    neighbors of the deleted vertex have to be exhibited. -/
theorem clique_cap_of_elimination {k m r n p q : Nat}
    (colors : Fin k → List Nat) (stamp : Nat → Nat)
    (F : Finset Nat)
    (proper : ∀ i : Fin k, (colors i).Pairwise (fun a b => edge n p q a b = false))
    (cover : ∀ a∈F, ∃ i : Fin k, a ∈ colors i)
    (edges : ∀ a∈F, ∀ b∈F, a≠b → edge n p q a b = true)
    (certificate : ∀ a∈F, stamp a < r → ∃ miss : Finset (Fin k), k - miss.card < m ∧
      ∀ i∈miss, ∀ b∈colors i, b ≠ a → stamp a ≤ stamp b → edge n p q a b = false)
    (residual : ∃ S : Finset Nat, S.card ≤ m ∧ ∀ a∈F, r ≤ stamp a → a∈S) :
    F.card ≤ m := by
  classical
  by_cases H : ∀ a∈F, r ≤ stamp a
  · obtain ⟨S,hS,h⟩ := residual
    exact (Finset.card_le_card (fun a ha => h a ha (H a ha))).trans hS
  · push Not at H
    obtain ⟨a, ha, lo⟩ := H
    obtain ⟨v,hv,mn⟩ := Finset.exists_min_image F stamp ⟨a,ha⟩
    have vl := lt_of_le_of_lt (mn a ha) lo
    obtain ⟨miss,cn,safe⟩ := certificate v hv vl
    let P := F.erase v
    have hp : P.card ≤ k - miss.card := by
      apply clique_cap_index colors miss le_rfl
      · exact proper
      · intro b hb
        have hbF := (Finset.mem_erase.mp hb).2
        obtain ⟨i,hic⟩ := cover b hbF
        refine ⟨i, ?_, hic⟩
        intro hi
        have nb := (Finset.mem_erase.mp hb).1
        have E := safe i hi b hic nb (mn b hbF)
        rw [edges v hv b hbF (Ne.symm nb)] at E
        contradiction
      · intro a aP b bP ne
        exact edges a (Finset.mem_of_mem_erase aP) b (Finset.mem_of_mem_erase bP) ne
    have h := Finset.card_erase_add_one hv
    change P.card+1=F.card at h
    omega

#print axioms clique_cap_of_elimination
end IU
