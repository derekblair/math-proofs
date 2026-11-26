import HaarClass6ParallelWords
import HaarAnyPorts
import HaarShortClosedIsCycle

namespace HaarClass6HighGirth
open HaarUniversal36 HaarAllNoncommuting HaarClass6ParallelWords
variable {G : Type*} [Group G]

theorem normalized (nil : L G 6=⊥) (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y)
    (below : ∀ k, 4≤k → k<34 → Even k → ¬HasCycle x y k) : HasCycle x y 64 :=
  HaarShortClosedIsCycle.fromWord x y hx hy hxy W (by decide) (by decide)
    (by decide) (close nil x y) (by decide) 34 (by decide) below

theorem any_ports (nil : L G 6=⊥) (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t)
    (below : ∀ k, 4≤k → k<34 → Even k → ¬HaarAnyPorts.HasPortCycle r s t k) :
    HaarAnyPorts.HasPortCycle r s t 64 := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  apply HaarAnyPorts.map_cycle r s t
  exact normalized nil (s*r⁻¹) (t*r⁻¹) a b c
    (fun k lo hi ev u => below k lo hi ev (HaarAnyPorts.map_cycle r s t u))

end HaarClass6HighGirth
#print axioms HaarClass6HighGirth.any_ports
