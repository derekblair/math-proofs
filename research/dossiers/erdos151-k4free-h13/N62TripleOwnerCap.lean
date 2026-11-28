import N62DCounts

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13 Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

theorem three_owner_double_cap
    (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (P Z : Finset V) (pc : P.card≤3) (ps : P⊆S) (zd : Z⊆F.doubles)
    (supp : ∀ z∈Z, support G S z⊆P) : Z.card≤P.card := by
  have zx : Z⊆X := fun z hz => (F.dblData z (zd hz)).1
  apply pairwiseLone_supported_count G sym irr S P Z sc ps sf upper (out.symm.mono_right zx) _ supp
  intro a ha b hb
  have ha2 := support_two G F (zd ha)
  have hb2 := support_two G F (zd hb)
  have sub : support G S a ∪ support G S b⊆P := union_subset (supp a ha) (supp b hb)
  have up := card_le_card sub
  have ct := card_union_add_card_inter (support G S a) (support G S b)
  obtain ⟨u,ui⟩ := card_pos.mp (show 0<(support G S a∩support G S b).card by omega)
  obtain ⟨ua,ub⟩ := mem_inter.mp ui
  exact ⟨u,near_double_lone_of_support G F (zd ha) ua,near_double_lone_of_support G F (zd hb) ub⟩

#print axioms three_owner_double_cap
end Erdos151N62
