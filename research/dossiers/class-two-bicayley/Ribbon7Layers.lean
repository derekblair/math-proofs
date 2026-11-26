import Ribbon6Family

namespace Ribbon7
open HaarUniversal36 HaarClass5Commute
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem commutes_L1 (i : Nat) (nil : L G (i+1+1)=⊥)
    {a b : G} (A : a ∈ L G i) (B : b ∈ L G 1) : Commute a b := by
  have le : L G 1 ≤ Subgroup.centralizer ({a}:Set G) := by
    change ⁅(⊤:Subgroup G),(⊤:Subgroup G)⁆ ≤ _
    apply Subgroup.commutator_le.mpr
    intro v _ w _
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (centralizes_commutator i nil A v w).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (le B)).symm

theorem comm_mem (i : Nat) {a b : G} (A : a ∈ L G i) (B : b ∈ L G 1) :
    ⁅a,b⁆ ∈ L G (i+1+1) := by
  let N := L G (i+1+1)
  let f := QuotientGroup.mk' N
  have M (j : Nat) : (L G j).map f = L (G⧸N) j := by
    rw [Subgroup.map_lowerCentralSeries,
      Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective N)]
  have nil : L (G⧸N) (i+1+1)=⊥ := by
    rw [← M,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  have a' : f a ∈ L (G⧸N) i := (M i) ▸ Subgroup.mem_map_of_mem f A
  have b' : f b ∈ L (G⧸N) 1 := (M 1) ▸ Subgroup.mem_map_of_mem f B
  apply (QuotientGroup.eq_one_iff (N:=N) _).mp
  change f ⁅a,b⁆=1
  rw [map_commutatorElement,(commutes_L1 i nil a' b').commutator_eq]

theorem last_central (i : Nat) (nil : L G (i+1)=⊥)
    {a : G} (A : a ∈ L G i) : ∀ b : G, Commute a b := by
  intro b
  apply commutatorElement_eq_one_iff_commute.mp
  have H := next A b
  rwa [nil,Subgroup.mem_bot] at H

end Ribbon7
#print axioms Ribbon7.comm_mem
