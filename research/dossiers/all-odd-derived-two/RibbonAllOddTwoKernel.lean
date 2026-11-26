import RibbonTwoFamily
import RibbonAllOddDerivedTwo

namespace RibbonTwo
open RibbonDerived3
variable {G : Type*} [Group G]

/-- An odd quotient satisfying the class-two-derived hypothesis yields
a dyadic cycle in the full group through any finite normal 2-subgroup.
There is no class or cardinality hypothesis on the ambient group. -/
theorem finite_odd_quotient (N : Subgroup G) [N.Normal] [Finite N] [Finite (G ⧸ N)]
    (two : IsPGroup 2 N) (cl : DLS (G ⧸ N) 2=⊥)
    (odd : Odd (Nat.card (G ⧸ N))) (x y : G) (hx : x^2≠1) (hy : y^2≠1) :
    ∃ r, 2≤r ∧ 2^r≤64 * Monoid.exponent N ∧ Ribbon.Cycle x y (2^r) := by
  apply quotient_bound64 N two x y hx hy
  intro hx' hy'
  exact RibbonAllOddDerivedTwo.finite_odd cl _ _ odd hx' hy'

end RibbonTwo
#print axioms RibbonTwo.finite_odd_quotient
