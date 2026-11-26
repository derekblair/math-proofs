import HaarC5OddCover
import HaarC5HaarGeometry

namespace HaarC5Haar
open HaarC5Voltage
variable {G : Type*} [Group G] (π : G →* Multiplicative (ZMod 5)) (x y : G)
variable (hx : (π x).toAdd=1) (hy : (π y).toAdd=2)
variable [hc : Fact (∀ (a b : π.ker), a*b=b*a)]
local instance commKernelFinal : CommGroup π.ker where
  __ := (inferInstance : Group π.ker)
  mul_comm := hc.out
local instance addCommKernelFinal : AddCommGroup (Additive π.ker) := inferInstance

include hx hy hc in
theorem haar_cycle (noTwo : ∀ a : Additive π.ker, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarAllNoncommuting.HasCycle x y n := by
  obtain ⟨n,hn,v,vinj,cv⟩ := HaarC5OddCover.any_cover (edgeVoltage π x y hx hy)
    (anti π x y hx hy) noTwo
  refine ⟨n,hn,point π x ∘ v,(point_inj π x hx).comp vinj,?_⟩
  intro i
  exact point_adj π x y hx hy (cv i)

include hx hy hc in
theorem kernel_odd [Finite G] (hodd : Odd (Nat.card π.ker)) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarAllNoncommuting.HasCycle x y n :=
  haar_cycle π x y hx hy (HaarC5OddCover.finite_odd_noTwo hodd)

end HaarC5Haar
#print axioms HaarC5Haar.kernel_odd
