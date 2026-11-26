import HaarAnyPorts
import HaarClass5GirthUpper
import HaarClass5DyadicHighGirth

namespace HaarClass5AnyPorts
open HaarAnyPorts HaarUniversal36

/-- Every three-port Haar graph over a group of nilpotency class at most five
has a simple even cycle of length between four and 36. No finiteness or
odd-order assumption is needed. -/
theorem even_cycle_le36 {G : Type*} [Group G] (nil : L G 5=⊥) (r s t : G)
    (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ k, 4≤k ∧ k≤36 ∧ Even k ∧ HasPortCycle r s t k := by
  obtain ⟨a,b,c⟩ := as_three r s t hr ht hs
  obtain ⟨k,lo,hi,even,cy⟩ :=
    HaarClass5GirthUpper.even_cycle_le36 (s*r⁻¹) (t*r⁻¹) a b c nil
  exact ⟨k,lo,hi,even,map_cycle r s t cy⟩

/-- At girth at least 34, a cyclically reduced 64-step walk is simple.
In this high-girth regime, 64 is the first power-of-two cycle length. -/
theorem high_girth_cycle64 {G : Type*} [Group G] (nil : L G 5=⊥) (r s t : G)
    (hr : r≠s) (ht : r≠t) (hs : s≠t)
    (below : ∀ k, 4≤k → k<34 → Even k → ¬ HasPortCycle r s t k) :
    HasPortCycle r s t 64 := by
  obtain ⟨a,b,c⟩ := as_three r s t hr ht hs
  apply map_cycle
  apply HaarClass5DyadicHighGirth.highGirth_has64 nil _ _ a b c
  intro k lo hi even hc
  exact below k lo hi even (map_cycle r s t hc)

end HaarClass5AnyPorts
#print axioms HaarClass5AnyPorts.even_cycle_le36
#print axioms HaarClass5AnyPorts.high_girth_cycle64
