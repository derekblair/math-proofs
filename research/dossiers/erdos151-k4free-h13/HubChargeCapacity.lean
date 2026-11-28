import ThreeHubCount
import OneShared
import Mathlib.Data.Finset.SDiff

namespace Erdos151H13
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A link of size at most eleven cannot contain three mutually
nonadjacent charged pivots, each with four neighbors and any two
sharing at most one. The supports of any three would occupy at least
nine vertices outside the three pivots. -/
theorem at_most_two_charged (S W : Finset V) (N : V → Finset V)
    (s11 : S.card ≤ 11) (wS : W ⊆ S)
    (inside : ∀ a ∈ W, N a ⊆ S \ W)
    (four : ∀ a ∈ W, 4 ≤ (N a).card)
    (overlap : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → (N a ∩ N b).card ≤ 1) :
    W.card ≤ 2 := by
  classical
  by_contra hbad
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<W.card by omega)
  have ec := Finset.card_erase_add_one ha
  obtain ⟨b,hb,c,hc,bc⟩ := pick_two (W.erase a) (by omega)
  obtain ⟨ba,hb⟩ := Finset.mem_erase.mp hb
  obtain ⟨ca,hc⟩ := Finset.mem_erase.mp hc
  have hUnion : ((N a ∪ N b) ∪ N c) ⊆ S \ W := by
    intro z hz
    rcases Finset.mem_union.mp hz with h|h
    · rcases Finset.mem_union.mp h with h|h
      · exact inside a ha h
      · exact inside b hb h
    · exact inside c hc h
  have hU := Finset.card_le_card hUnion
  have ws := Finset.card_sdiff_add_card_eq_card wS
  have eq := three_union_card (N a) (N b) (N c)
  have f1 := four a ha
  have f2 := four b hb
  have f3 := four c hc
  have o1 := overlap a ha b hb ba.symm
  have o2 := overlap a ha c hc ca.symm
  have o3 := overlap b hb c hc bc
  omega

#print axioms at_most_two_charged
end Erdos151H13
