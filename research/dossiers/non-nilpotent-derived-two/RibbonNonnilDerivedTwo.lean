import RibbonP11Combined
import RibbonStationaryFieldCover
import RibbonStationaryClass2API

namespace RibbonNonnilDerivedTwo
open RibbonDerived3
universe u

/-- A finite group of order coprime to six whose derived subgroup has
nilpotency class at most two yields a simple cycle of power-of-two length
at most 64 in its one-matching bi-Cayley graph. Ambient nilpotence and
generation by the two rim elements are not required. -/
theorem finite_coprime_six {G : Type u} [Group G] [Finite G]
    (dnil : DLS G 2=⊥) (x y : G) (odd : Odd (Nat.card G))
    (no3 : ¬3 ∣ Nat.card G) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  exact RibbonP11Adapters.finite_from_fields RibbonStationaryField.field_cover.{u,u}
    RibbonStationaryField.field_cover.{u,0}
    (RibbonStationary.derived_class_two_iff.mp dnil) x y odd no3 hx hy

end RibbonNonnilDerivedTwo
#print axioms RibbonNonnilDerivedTwo.finite_coprime_six
