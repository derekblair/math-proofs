import HaarMetaNineOddCover
import HaarMetaNineHaarGeometry

namespace HaarMetaNineHaar
open HaarMetaNineVoltage
variable {G : Type*} [Group G] (π : G →* Multiplicative (ZMod 9)) (x y : G)
variable (hx : (π x).toAdd=1) (hy : (π y).toAdd=3)
variable (surj : Function.Surjective π)
variable [hc : Fact (∀ (a b : π.ker), a*b=b*a)]
local instance commKernelFinal : CommGroup π.ker where
  __ := (inferInstance : Group π.ker)
  mul_comm := hc.out
local instance addCommKernelFinal : AddCommGroup (Additive π.ker) := inferInstance

include hx hy hc surj in
theorem haar_cycle (noTwo : ∀ a : Additive π.ker, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarAllNoncommuting.HasCycle x y n := by
  obtain ⟨n,hn,v,vinj,cv⟩ := HaarMetaNineOddCover.any_cover (edgeVoltage π x y surj hx hy)
    (anti π x y surj hx hy) noTwo
  refine ⟨n,hn,point π surj ∘ v,(point_inj π surj).comp vinj,?_⟩
  intro i
  exact point_adj π x y surj hx hy (cv i)

include hx hy hc surj in
theorem kernel_odd [Finite G] (hodd : Odd (Nat.card π.ker)) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarAllNoncommuting.HasCycle x y n :=
  haar_cycle π x y hx hy surj (HaarMetaNineOddCover.finite_odd_noTwo hodd)

end HaarMetaNineHaar
#print axioms HaarMetaNineHaar.kernel_odd
