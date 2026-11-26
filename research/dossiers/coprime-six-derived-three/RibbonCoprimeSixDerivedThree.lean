import RibbonD3FieldInverseAdapter
import RibbonD3FieldInversion
import RibbonD3FiniteDone
import RibbonD3Stationary
import RibbonD3MixedSmall
import RibbonP11Adapters

namespace RibbonCoprimeSixDerivedThree
open RibbonD3Stationary RibbonD3Finite RibbonDerived3
universe u

/-- A finite group of order prime to six whose derived subgroup has
nilpotency class at most three has a dyadic cycle of length at most 128
in each nondegenerate one-matching bi-Cayley graph. Ambient nilpotence
and generation by the two rim generators are not required. -/
theorem finite_coprime_six {G : Type u} [Group G] [Finite G]
    (d3 : DLS G 3=⊥) (x y : G)
    (odd : Odd (Nat.card G)) (no3 : ¬3∣Nat.card G) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 :=
  from_covers (field_from_inverse (@RibbonD3Field.inversion_cover)) all_pairs all_jets
    RibbonP11Adapters.meta_cover (nonstationary_cover RibbonD3Low.mixed_small)
    d3 x y odd no3 hx hy

end RibbonCoprimeSixDerivedThree
#print axioms RibbonCoprimeSixDerivedThree.finite_coprime_six
