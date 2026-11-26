import RibbonTwoKernel
import RibbonP3Odd

namespace RibbonTwo
variable {G : Type*} [Group G]

private theorem powers64 (x y : G) (h : RibbonP3.Good x y) :
    ∃ r, 2≤r ∧ r≤6 ∧ Ribbon.Cycle x y (2^r) := by
  rcases h with h|h|h|h|h
  · exact ⟨2,by decide,by decide,h⟩
  · exact ⟨3,by decide,by decide,h⟩
  · exact ⟨4,by decide,by decide,h⟩
  · exact ⟨5,by decide,by decide,h⟩
  · exact ⟨6,by decide,by decide,h⟩

/-- Transfer a quotient bound of 64 to a dyadic bound of
64 times the exponent of a finite normal 2-subgroup. -/
theorem quotient_bound64 (N : Subgroup G) [N.Normal] [Finite N]
    (two : IsPGroup 2 N) (x y : G) (hx : x^2≠1) (hy : y^2≠1)
    (base : (QuotientGroup.mk' N) x≠1 → (QuotientGroup.mk' N) y≠1 →
      RibbonP3.Good ((QuotientGroup.mk' N) x) ((QuotientGroup.mk' N) y)) :
    ∃ r, 2≤r ∧ 2^r≤64 * Monoid.exponent N ∧ Ribbon.Cycle x y (2^r) :=
  quotient_bound N two x y 6 hx hy (fun hx hy => powers64 _ _ (base hx hy))

end RibbonTwo
#print axioms RibbonTwo.quotient_bound64
