import HaarMetaTorsionOneGeometry
import HaarMetaTorsionOneRealCover

namespace HaarMetaTorsionOneHaar
open HaarAllNoncommuting HaarMetaVoltagePullback HaarMetaTorsionOneGeometry
variable {G Q : Type*} [Group G] [CommGroup Q]
variable (f : G→*Q) [hc : Fact (∀ a b : f.ker, a*b=b*a)]
local instance commK : CommGroup f.ker where
  __ := (inferInstance : Group f.ker)
  mul_comm := hc.out

theorem odd_cylinder [Finite G] (odd : Odd (Nat.card G)) (x y z t : G)
    (px : f x=f t) (py : f y=f z) (ht : (f t)^(3:ℕ)=1)
    (inj : Function.Injective (fun u : Fin 4 × Fin 3 => f (z^u.1.val*t^u.2.val))) :
    ∃ n, n∈[4,8,16,32] ∧ HasCycle x y n := by
  let S := setup f x y z t px py ht inj
  have no : ∀ a : Additive f.ker, a+a=0 → a=0 :=
    HaarMetaTorsionOneOddCover.finite_odd_noTwo (Odd.of_dvd_nat odd f.ker.card_subgroup_dvd_card)
  obtain ⟨n,h,e⟩ := HaarMetaTorsionOneRealCover.any_cover (weight S) (anti S) no
  exact ⟨n,h,lift_cycle S e⟩

end HaarMetaTorsionOneHaar
#print axioms HaarMetaTorsionOneHaar.odd_cylinder
