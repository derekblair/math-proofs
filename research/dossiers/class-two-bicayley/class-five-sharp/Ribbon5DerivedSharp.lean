import Ribbon5Complete
import Ribbon5PortClass
import Ribbon7Layers
import RibbonDerivedTwoClose

namespace Ribbon5UT
open HaarMatrixCycle (UT)
open HaarUniversal36 HaarClass4Structure
open scoped commutatorElement

theorem class_five_derived_two {G : Type*} [Group G] (nil : L G 5=⊥) :
    RibbonDerivedTwo.D2 G := by
  intro a ha b hb z hz
  exact Ribbon7.commutes_L1 3 nil (Ribbon7.comm_mem 1 ha hb) hz

theorem class_five_sharp_for_derived_two :
    RibbonDerivedTwo.D2 UT ∧ Odd (Nat.card UT) ∧
      (L UT 5 = ⊥) ∧ (L UT 4 ≠ ⊥) ∧
        ¬ ComponentCycle 4 ∧ ¬ ComponentCycle 8 ∧ ¬ ComponentCycle 16 ∧
          ¬ ComponentCycle 32 ∧ ComponentCycle 64 :=
  ⟨class_five_derived_two exact_five.1,odd,exact_five.1,exact_five.2,
    fully_verified_sharp_component⟩

end Ribbon5UT
#print axioms Ribbon5UT.class_five_sharp_for_derived_two
