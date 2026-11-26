import HaarHoneyRealCover
import HaarHoneyNoShort
import Mathlib.GroupTheory.Coset.Card

namespace HaarHoneyHaar
open HaarHoneyVoltage HaarAllNoncommuting
variable {G Q : Type*} [Group G] [Group Q]
variable (f : G →* Q) (x y : G) (cm : Commute (f x) (f y))
variable [hc : Fact (∀ (a b : f.ker), a*b=b*a)]
local instance commK : CommGroup f.ker where
  __ := (inferInstance : Group f.ker)
  mul_comm := hc.out
local instance addCommK : AddCommGroup (Additive f.ker) := inferInstance

include cm hc in
theorem injected_grid (inj : Function.Injective (fun t : Fin 16 => f (rep0 x y t)))
    (noTwo : ∀ a : Additive f.ker, a+a=0 → a=0) :
    ∃ n, n ∈ [16,32] ∧ HasCycle x y n := by
  obtain ⟨n,hn,v,vinj,cv⟩ :=
    HaarHoneyRealCover.any_cover (weight f x y cm) (anti f x y cm) noTwo
  refine ⟨n,hn,point f x y ∘ v,(point_inj f x y inj).comp vinj,?_⟩
  intro i
  obtain ⟨h,j,hj,eq⟩ := cv i
  exact point_edge f x y cm h j hj eq

include cm hc in
theorem odd_no_short [Finite G] (odd : Odd (Nat.card G))
    (nh : noShort (f x) (f y)) : ∃ n, n ∈ [16,32] ∧ HasCycle x y n :=
  injected_grid f x y cm (grid_of_noShort f x y cm nh)
    (HaarHoneyOddCover.finite_odd_noTwo (Odd.of_dvd_nat odd (Subgroup.card_subgroup_dvd_card f.ker)))

end HaarHoneyHaar
#print axioms HaarHoneyHaar.odd_no_short
