import RibbonMetaFinal
import RibbonClass3Sharp
import RibbonClass3SharpComponent

namespace RibbonMeta
open HaarClass4Structure HaarClass5Commute RibbonClass3SharpGraph
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem meta_of_class_three (nil : LS G 3=⊥) : Meta G := by
  intro a ha b hb
  have le : LS G 1 ≤ Subgroup.centralizer ({a}:Set G) := by
    change ⁅(⊤:Subgroup G),(⊤:Subgroup G)⁆ ≤ _
    apply Subgroup.commutator_le.mpr
    intro v _ w _
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (centralizes_commutator 1 nil ha v w).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (le hb)).symm

/-- The class-three UT₄(F₁₁) witness is an odd nilpotent metabelian
ribbon with no simple C4, C8 or C16 and with a simple C32. -/
theorem metabelian_sharp :
    Meta H ∧ (∃ n, LS H n=⊥) ∧ Odd (Nat.card H) ∧ a≠1 ∧ b≠1 ∧
      ¬ Ribbon.Cycle a b 4 ∧ ¬ Ribbon.Cycle a b 8 ∧
      ¬ Ribbon.Cycle a b 16 ∧ Ribbon.Cycle a b 32 := by
  exact ⟨meta_of_class_three class_three,⟨3,class_three⟩,by rw [h_card]; decide,
    (by decide : a≠1),(by decide : b≠1),sharp⟩

end RibbonMeta
#print axioms RibbonMeta.meta_of_class_three
#print axioms RibbonMeta.metabelian_sharp
