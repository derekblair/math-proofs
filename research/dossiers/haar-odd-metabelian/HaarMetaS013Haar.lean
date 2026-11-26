import HaarMetaS013Geometry
import HaarMetaS013RealCover

namespace HaarMetaS013Haar
open HaarAllNoncommuting HaarMetaVoltagePullback HaarMetaS013Geometry
variable {G Q : Type*} [Group G] [Group Q]
variable (f : G→*Q) [hc : Fact (∀ a b : f.ker, a*b=b*a)]
local instance commK : CommGroup f.ker where
  __ := (inferInstance : Group f.ker)
  mul_comm := hc.out

theorem odd_strip [Finite G] (odd : Odd (Nat.card G)) (x y z : G)
    (px : f x=(f z)^(1:ℕ)) (py : f y=(f z)^(3:ℕ)) (large : 10≤orderOf (f z)) :
    ∃ n, n∈[4,8,16,32] ∧ HasCycle x y n := by
  let T := setup f x y z px py (inject_of_order f z large)
  have no : ∀ a : Additive f.ker, a+a=0 → a=0 :=
    HaarMetaS013OddCover.finite_odd_noTwo (Odd.of_dvd_nat odd f.ker.card_subgroup_dvd_card)
  obtain ⟨n,h,e⟩ := HaarMetaS013RealCover.any_cover (weight T) (anti T) no
  exact ⟨n,h,lift_cycle T e⟩

end HaarMetaS013Haar
#print axioms HaarMetaS013Haar.odd_strip
