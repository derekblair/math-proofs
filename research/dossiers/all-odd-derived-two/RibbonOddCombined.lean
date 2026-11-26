import RibbonOddStationary
import RibbonOddPairUse
import RibbonOddJetUse
import RibbonOddMixed
import RibbonStationaryClass2API

namespace RibbonOddFinite
open RibbonDerived3
universe u

/-- The all-odd graph theorem, with only the universal field separation
certificate left as a parameter. All residual geometry is discharged. -/
theorem from_field {G : Type u} [Group G] [Finite G]
    (cover : RibbonOdd.FieldCover.{u,u} Bad)
    (dnil : DLS G 2=⊥) (x y : G) (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 :=
  RibbonOdd.finite_odd_derived2_of_covers cover pairs_cover jets_cover RibbonP11Adapters.meta_cover
    (mixed_from_field cover) (RibbonStationary.derived_class_two_iff.mp dnil) x y odd hx hy

end RibbonOddFinite
#print axioms RibbonOddFinite.from_field
