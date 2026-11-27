import HaarStripRealCover
import HaarStripHaarGeometry
import Mathlib.GroupTheory.Coset.Card

namespace HaarStripHaar
open HaarStripVoltage HaarAllNoncommuting
variable {G Q : Type*} [Group G] [Group Q]
variable (f : G →* Q) (x y : G) (sq : f y=(f x)^2)
variable [hc : Fact (∀ (a b : f.ker), a*b=b*a)]
local instance commK : CommGroup f.ker where
  __ := (inferInstance : Group f.ker)
  mul_comm := hc.out
local instance addCommK : AddCommGroup (Additive f.ker) := inferInstance

include sq hc in
theorem injected_strip (inj : Function.Injective (fun t : Fin 6 => f (rep0 x t)))
    (noTwo : ∀ a : Additive f.ker, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle x y n := by
  obtain ⟨n,hn,v,vinj,cv⟩ :=
    HaarStripRealCover.any_cover (weight f x y sq) (anti f x y sq) noTwo
  refine ⟨n,hn,point f x ∘ v,(point_inj f x inj).comp vinj,?_⟩
  intro i
  obtain ⟨h,j,hj,eq⟩ := cv i
  exact point_edge f x y sq h j hj eq

include sq hc in
theorem odd_ap [Finite G] (odd : Odd (Nat.card G)) (large : 6≤orderOf (f x)) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle x y n := by
  have inj : Function.Injective (fun t : Fin 6 => f (rep0 x t)) := by
    intro i j h
    apply Fin.ext
    have hi : i.val ∈ Set.Iio (orderOf (f x)) := lt_of_lt_of_le i.isLt large
    have hj : j.val ∈ Set.Iio (orderOf (f x)) := lt_of_lt_of_le j.isLt large
    exact pow_injOn_Iio_orderOf hi hj (by simpa only [rep0,map_pow] using h)
  exact injected_strip f x y sq inj
    (HaarStripOddCover.finite_odd_noTwo (Odd.of_dvd_nat odd (Subgroup.card_subgroup_dvd_card f.ker)))

end HaarStripHaar
#print axioms HaarStripHaar.odd_ap
