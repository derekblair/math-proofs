import HaarMetaTorusOddCover
import HaarMetaTorusHaarGeometry

namespace HaarMetaTorusHaar
open HaarMetaTorusVoltage
variable {G : Type*} [Group G] (π : G →* Multiplicative ((ZMod 3 × ZMod 3))) (x y : G)
variable (hx : (π x).toAdd=(0,1)) (hy : (π y).toAdd=(1,0))
variable (surj : Function.Surjective π)
variable [hc : Fact (∀ (a b : π.ker), a*b=b*a)]
local instance commKernelFinal : CommGroup π.ker where
  __ := (inferInstance : Group π.ker)
  mul_comm := hc.out
local instance addCommKernelFinal : AddCommGroup (Additive π.ker) := inferInstance

include hx hy hc surj in
theorem haar_cycle (noTwo : ∀ a : Additive π.ker, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarAllNoncommuting.HasCycle x y n := by
  obtain ⟨n,hn,v,vinj,cv⟩ := HaarMetaTorusOddCover.any_cover (edgeVoltage π x y surj hx hy)
    (anti π x y surj hx hy) noTwo
  refine ⟨n,hn,point π surj ∘ v,(point_inj π surj).comp vinj,?_⟩
  intro i
  exact point_adj π x y surj hx hy (cv i)

include hx hy hc surj in
theorem kernel_odd [Finite G] (hodd : Odd (Nat.card π.ker)) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarAllNoncommuting.HasCycle x y n :=
  haar_cycle π x y hx hy surj (HaarMetaTorusOddCover.finite_odd_noTwo hodd)

end HaarMetaTorusHaar
#print axioms HaarMetaTorusHaar.kernel_odd
