import RibbonP11Adapters
import RibbonP11Stationary
import RibbonStationaryLocal

namespace RibbonP11Adapters
open RibbonP11 HaarClass4Structure
universe u

theorem nonstationary_cover : NonStationaryCover.{u} := by
  intro G _ _ d2 x y _ odd no3 _ _ h
  apply Or.inr ∘ Or.inr ∘ Or.inr
  have c := RibbonStationary.nontrivial_projected (dnil d2) x y odd no3
  exact c (fun e => h ((QuotientGroup.eq_one_iff _).mp e))

/-- Everything except the universal finite-field separation certificate.
The two occurrences of the field callback differ only in universe. -/
theorem finite_from_fields {G : Type u} [Group G] [Finite G]
    (check : FieldCover.{u,u} Bad) (checkSmall : FieldCover.{u,0} Bad)
    (d2 : RibbonDerivedTwo.D2 G) (x y : G) (odd : Odd (Nat.card G))
    (no3 : ¬3∣Nat.card G) (hx : x≠1) (hy : y≠1) : Good x y :=
  finite_odd_derived2_of_covers check checkSmall pair_cover jet_cover meta_cover nonstationary_cover
    d2 x y odd no3 hx hy

end RibbonP11Adapters
#print axioms RibbonP11Adapters.finite_from_fields
