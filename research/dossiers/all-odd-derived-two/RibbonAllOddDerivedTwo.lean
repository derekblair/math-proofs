import RibbonOddCombined
import RibbonAllOddFieldCover

namespace RibbonAllOddDerivedTwo
open RibbonDerived3
universe u

/-- The sharp 64 bound for one-matching bi-Cayley graphs over finite
odd-order groups whose derived subgroup has nilpotency class at most two.
Neither ambient nilpotence nor generation by the rim elements is assumed. -/
theorem finite_odd {G : Type u} [Group G] [Finite G]
    (dnil : DLS G 2=⊥) (x y : G) (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 :=
  RibbonOddFinite.from_field RibbonAllOddField.field_cover.{u,u} dnil x y odd hx hy

end RibbonAllOddDerivedTwo
#print axioms RibbonAllOddDerivedTwo.finite_odd
