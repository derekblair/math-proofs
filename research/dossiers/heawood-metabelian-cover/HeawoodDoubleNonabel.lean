import HeawoodDoubleCover
import HeawoodCoverChart

namespace HeawoodDoubleDeck
open HeawoodDouble
open HaarOrbitC7Voltage (B)
open HeawoodCoverChart (RegularAbelianCover)
open scoped commutatorElement

theorem not_abelian : ¬ ∀ a b : Deck, a*b=b*a := by
  intro cm
  let g : Group Deck := inferInstance
  letI : CommGroup Deck := { g with mul_comm := cm }
  let C : RegularAbelianCover (Additive Deck) V2 := {
    adj := Edge2
    symm := HomologyThree.liftSymm Edge1 first_symm
    proj := base
    onto := onto
    act := fun a => action a.toMul
    zero_act := action_one
    add_act := action_mul
    fiber_pres := action_projects
    edge_pres := action_edge
    fiber_torsor := fun {u v} h => action_regular u v h
    edge_proj := edge_to_base
    edge_lift := fun u b e => by
      obtain ⟨w,hw,un⟩ := unique_lift u b e
      exact ⟨w,hw.symm,fun y hy => un y hy.symm⟩ }
  obtain ⟨n,hn,v,iv,ev⟩ := C.dyadic_cycle
  have l := second_lower n (by simp at hn; omega) ⟨v,iv,ev⟩
  simp at hn
  omega

theorem commutator_nontrivial : commutator Deck ≠ ⊥ := by
  intro h
  apply not_abelian
  intro a b
  have c : ⁅a,b⁆ ∈ commutator Deck :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [h] at c
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp c)

end HeawoodDoubleDeck
#print axioms HeawoodDoubleDeck.commutator_nontrivial
