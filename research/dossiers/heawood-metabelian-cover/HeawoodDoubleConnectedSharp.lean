import HeawoodDoubleSharp
import HeawoodDoubleComponent

namespace HeawoodDoubleComponent
open HeawoodDouble HaarDerivedFlowPositive
open HaarOrbitC7Voltage (B)
open HeawoodCoverChart (RegularAbelianCover)
open scoped commutatorElement

theorem component_not_abelian (o : V2) : ¬∀ a b : stabilizer o, a*b=b*a := by
  intro cm
  let g : Group (stabilizer o) := inferInstance
  letI : CommGroup (stabilizer o) := {g with mul_comm := cm}
  let C : RegularAbelianCover (Additive (stabilizer o)) (Component o) := {
    adj := adj
    symm := fun e => edge_symm e
    proj := proj
    onto := onto o
    act := fun a => act a.toMul
    zero_act := act_one
    add_act := act_mul
    fiber_pres := act_projects
    edge_pres := act_edges
    fiber_torsor := fun {u v} h => act_regular u v h
    edge_proj := project_adj
    edge_lift := fun u b e => by
      obtain ⟨w,hw,un⟩ := unique_lift u b e
      exact ⟨w,hw.symm,fun y hy => un y hy.symm⟩ }
  obtain ⟨n,hn,v,vi,ve⟩ := C.dyadic_cycle
  have big := second_lower n (by simp at hn;omega)
    ((cycles_iff o n (by simp at hn;omega)).mp ⟨v,vi,ve⟩)
  simp at hn
  omega

/-- Every component of the double mod-3 Heawood lift is a connected regular
cover with finite odd metabelian nonabelian deck, ordinary girth 54, and
least dyadic simple cycle length 64. -/
theorem connected_sharp (o : V2) :
    Odd (Nat.card (stabilizer o)) ∧
    (∀ a b : commutator (stabilizer o), a*b=b*a) ∧
    (¬∀ a b : stabilizer o, a*b=b*a) ∧
    (Cyclic (@adj o) 54 ∧ ∀ n, 3≤n → Cyclic (@adj o) n → 54≤n) ∧
    (Cyclic (@adj o) 64 ∧ ∀ n ∈ [4,8,16,32], ¬Cyclic (@adj o) n) := by
  refine ⟨odd_deck o,metabelian_deck o,component_not_abelian o,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact (cycles_iff o 54 (by decide)).mpr second_upper
  · intro n hn cv
    exact second_lower n hn ((cycles_iff o n (by omega)).mp cv)
  · exact (cycles_iff o 64 (by decide)).mpr smallest_dyadic.1
  · intro n hn cv
    have p : 0<n := by simp at hn;omega
    exact smallest_dyadic.2 n hn ((cycles_iff o n p).mp cv)

end HeawoodDoubleComponent
#print axioms HeawoodDoubleComponent.connected_sharp
