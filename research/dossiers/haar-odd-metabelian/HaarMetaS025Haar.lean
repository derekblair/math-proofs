import HaarMetaS025Geometry
import HaarMetaS025RealCover

namespace HaarMetaS025Haar
open HaarAllNoncommuting HaarMetaVoltagePullback HaarMetaS025Geometry
variable {G Q : Type*} [Group G] [Group Q]
variable (f : G→*Q) [hc : Fact (∀ a b : f.ker, a*b=b*a)]
local instance commK : CommGroup f.ker where
  __ := (inferInstance : Group f.ker)
  mul_comm := hc.out

theorem odd_strip [Finite G] (odd : Odd (Nat.card G)) (x y z : G)
    (px : f x=(f z)^(2:ℕ)) (py : f y=(f z)^(5:ℕ)) (large : 13≤orderOf (f z)) :
    ∃ n, n∈[4,8,16,32] ∧ HasCycle x y n := by
  let T := setup f x y z px py (inject_of_order f z large)
  have no : ∀ a : Additive f.ker, a+a=0 → a=0 :=
    HaarMetaS025OddCover.finite_odd_noTwo (Odd.of_dvd_nat odd f.ker.card_subgroup_dvd_card)
  obtain ⟨n,h,e⟩ := HaarMetaS025RealCover.any_cover (weight T) (anti T) no
  exact ⟨n,h,lift_cycle T e⟩

end HaarMetaS025Haar
#print axioms HaarMetaS025Haar.odd_strip
