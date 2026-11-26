import RibbonStationaryFieldAdapter

namespace RibbonStationary
open RibbonDerived3 HaarClass4Structure
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- Convert both arrow directions between the class-two derived subgroup
condition and the explicit central-commutator interface of the P11 package. -/
theorem derived_class_two_iff : DLS G 2=⊥ ↔ RibbonDerivedTwo.D2 G := by
  constructor
  · intro h a ha b hb z hz
    have H : ⁅a,b⁆∈DLS G 1 := Subgroup.commutator_mem_commutator ha hb
    have A : ⁅⁅a,b⁆,z⁆∈DLS G 2 := Subgroup.commutator_mem_commutator H hz
    rw [h,Subgroup.mem_bot] at A
    exact commutatorElement_eq_one_iff_commute.mp A
  · exact RibbonP11Adapters.dnil

end RibbonStationary
#print axioms RibbonStationary.derived_class_two_iff
