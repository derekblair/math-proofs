import RibbonD3DerivedNoThreeFinal
import RibbonD3OddFieldAdapter
import RibbonD3WidePairJet

namespace RibbonD3DerivedNoThree
open RibbonDerived3
universe u

/-- No ambient prime-to-three hypothesis. The derived subgroup has
    nilpotency class at most three and order not divisible by three. -/
theorem finite_odd_derived_three_no3 {G : Type u} [Group G] [Finite G]
    (no3 : ¬ 3 ∣ Nat.card (commutator G))
    (d3 : DLS G 3=⊥) (x y : G) (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) :
    RibbonD3Odd.WideGood x y :=
  finite_odd_derived_three_no3_of_covers no3
    RibbonD3Odd.field_from_wide_inverse
    RibbonD3WideFinite.pair_cover RibbonD3WideFinite.jet_cover
    d3 x y odd hx hy

end RibbonD3DerivedNoThree
#print axioms RibbonD3DerivedNoThree.finite_odd_derived_three_no3
