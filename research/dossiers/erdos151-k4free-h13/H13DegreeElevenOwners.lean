import H12DegreeTenOwners
namespace Erdos151H12
open Erdős151 Erdos151Ramsey
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V] (G : V → V → Prop)
theorem privatePool_alpha_two_h13 (sym : ∀ {a b}, G a b → G b a)
    (S B : Finset V) (h10 : S.card=11) (hS : Free (Forbidden G) (S : Set V))
    (hB : Disjoint B S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 12)
    (u : V) (hu : u∈S) : AlphaCap G (privatePool G S B u) 2 := by
  intro T hT hInd
  let R := S.erase u
  have hR : (R : Set V) = (S : Set V) \ {u} := by
    ext x
    simp [R,Finset.mem_erase,and_comm]
  have freeR : Free (Forbidden G) (R : Set V) :=
    fun A hA hsub => hS A hA (fun _ hx => Finset.mem_of_mem_erase (hsub hx))
  have freeRT : Free (Forbidden G) ((R ∪ T : Finset V) : Set V) := by
    rw [Finset.coe_union]
    apply free_add_independent (Forbidden G) G _ _
      (fun A hA x hx y hy hne => forbidden_clique G sym A hA x y hx hy hne) freeR
    · exact fun x hx y hy _ => hInd x hx y hy
    · intro x hx
      rw [hR]
      exact ((mem_ps (G:=G) S x).mp ((mem_privatePool G).mp (hT hx)).2).2
  have hd : Disjoint R T := Finset.disjoint_left.mpr (fun x hx hxT =>
    Finset.disjoint_left.mp hB ((mem_privatePool G).mp (hT hxT)).1
      (Finset.mem_of_mem_erase hx))
  have hcr := Finset.card_erase_add_one hu
  change R.card+1 = S.card at hcr
  have cap := upper _ freeRT
  rw [Finset.card_union_of_disjoint hd] at cap
  omega

theorem degreeEleven_private_capacity_h13 [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (tf : TriangleFreeLinks G)
    (S B : Finset V) (h10 : S.card=11) (hS : Free (Forbidden G) (S : Set V))
    (hB : Disjoint B S)
    (blocked : ∀ x∈B, ¬ Free (Forbidden G) (insert x (S : Set V)))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 12)
    (u : V) (hu : u∈S) :
    2*(privatePool G S B u).card + 3*(lonePrivatePool G S B u).card ≤ 10 := by
  let R (a b : V) : Prop := G u a ∧ G u b ∧ G a b
  letI : DecidableRel R := fun a b => inferInstanceAs (Decidable (G u a ∧ G u b ∧ G a b))
  have rs : ∀ {a b}, R a b → R b a := fun h => ⟨h.2.1,h.1,sym h.2.2⟩
  have ri : ∀ a, ¬ R a a := fun a h => irr a h.2.2
  have rt : TriangleFree R :=
    fun a b c hab hbc hac => tf u a b c hab.1 hab.2.1 hbc.2.1 hab.2.2 hbc.2.2 hac.2.2
  have pi := privatePool_isolated G sym S B hS hB blocked u
  have hi : IsolatedIn R (lonePrivatePool G S B u) (privatePool G S B u) :=
    ⟨pi.1,fun x hx y hy h => pi.2 x hx y hy h.2.2⟩
  have hc : AlphaCap R (privatePool G S B u) 2 := by
    intro T hT hI
    apply privatePool_alpha_two_h13 G sym S B h10 hS hB upper u hu T hT
    exact fun a ha b hb hab => hI a ha b hb
      ⟨privatePool_adjacent G sym S B hS hB blocked u a (hT ha),
       privatePool_adjacent G sym S B hS hB blocked u b (hT hb),hab⟩
  exact private_d9 R rs ri rt hi hc

end Erdos151H12
