import HaarCycle
import Ribbon

namespace Ribbon5Bridge
abbrev P := Fin 3
abbrev Q := Bool × HaarCycle.Coord

def push (s : Q) (p : P) : Q :=
  if p=2 then (!s.1,s.2)
  else if s.1 then
    if p=0 then (s.1,HaarCycle.rightY s.2)
    else (s.1,s.2.1,s.2.2.1-1,s.2.2.2-s.2.1)
  else if p=0 then (s.1,HaarCycle.rightX s.2)
    else (s.1,s.2.1-1,s.2.2.1,s.2.2.2)

def gap (d : ℤ) : Prop :=
  d=1 ∨ d= -1 ∨ d=2 ∨ d= -2 ∨ d=3 ∨ d= -3 ∨ d=4 ∨ d= -4
instance (d : ℤ) : Decidable (gap d) := by unfold gap; infer_instance

def separated (u v : Q) : Prop :=
  u.1 ≠ v.1 ∨ gap (u.2.1-v.2.1) ∨ gap (u.2.2.1-v.2.2.1) ∨
    (u.2.1=v.2.1 ∧ u.2.2.1=v.2.2.1 ∧ gap (u.2.2.2-v.2.2.2))
instance (u v : Q) : Decidable (separated u v) := by unfold separated; infer_instance

/-- The 7 ends/points of the two copies of the connecting bridge.
Indices from the pair are ordered increasingly; at the first bridge end
the mate is the original vertex 0, not the closing endpoint 64. -/
def mate (i j : Nat) : Prop :=
  (i = 0 ∧ j = 26) ∨ (27 ≤ i ∧ i ≤ 32 ∧ i + j = 90)
instance (i j : Nat) : Decidable (mate i j) := by unfold mate; infer_instance

set_option maxRecDepth 16000
set_option maxHeartbeats 1600000


def tab32 : Array Q := #[(false, 0, 0, 0), (false, -1, 0, 0), (true, -1, 0, 0), (true, -1, 1, -1), (true, -1, 2, -2), (false, -1, 2, -2), (false, 0, 2, -2), (false, 1, 2, -2), (true, 1, 2, -2), (true, 1, 1, -3), (false, 1, 1, -3), (false, 0, 1, -3), (false, -1, 1, -3), (true, -1, 1, -3), (true, -1, 0, -2), (false, -1, 0, -2), (false, 0, 0, -2), (false, 1, 0, -2), (true, 1, 0, -2), (true, 1, 1, -1), (true, 1, 2, 0), (false, 1, 2, 0), (false, 0, 2, 0), (false, -1, 2, 0), (true, -1, 2, 0), (true, -1, 1, 1), (false, -1, 1, 1), (false, 0, 1, 1), (false, 1, 1, 1), (true, 1, 1, 1), (true, 1, 0, 0), (false, 1, 0, 0), (false, 0, 0, 0)]

def word32 : Array P := #[1,2,0,0,2,0,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1]

theorem step32 : ∀ i : Fin 32, push tab32[i.val]! word32[i.val]! = tab32[i.val+1]! := by decide +kernel

theorem closed32 : tab32[32]! = tab32[0]! := by decide +kernel

theorem chart32 : ∀ i j : Fin 32, i.val<j.val → separated tab32[i.val]! tab32[j.val]! := by decide +kernel

def tab64 : Array Q := #[(false, 0, 0, 0), (false, -1, 0, 0), (true, -1, 0, 0), (true, -1, 1, -1), (true, -1, 2, -2), (false, -1, 2, -2), (false, 0, 2, -2), (true, 0, 2, -2), (true, 0, 1, -2), (false, 0, 1, -2), (false, -1, 1, -2), (true, -1, 1, -2), (true, -1, 0, -1), (false, -1, 0, -1), (false, 0, 0, -1), (true, 0, 0, -1), (true, 0, 1, -1), (true, 0, 2, -1), (false, 0, 2, -1), (false, -1, 2, -1), (true, -1, 2, -1), (true, -1, 1, 0), (false, -1, 1, 0), (false, 0, 1, 0), (true, 0, 1, 0), (true, 0, 0, 0), (false, 0, 0, 0), (false, 1, 0, 0), (true, 1, 0, 0), (true, 1, 1, 1), (true, 1, 2, 2), (false, 1, 2, 2), (false, 0, 2, 2), (true, 0, 2, 2), (true, 0, 3, 2), (false, 0, 3, 2), (false, -1, 3, 2), (true, -1, 3, 2), (true, -1, 4, 1), (false, -1, 4, 1), (false, 0, 4, 1), (true, 0, 4, 1), (true, 0, 3, 1), (true, 0, 2, 1), (false, 0, 2, 1), (false, -1, 2, 1), (true, -1, 2, 1), (true, -1, 3, 0), (false, -1, 3, 0), (false, 0, 3, 0), (true, 0, 3, 0), (true, 0, 4, 0), (false, 0, 4, 0), (false, -1, 4, 0), (true, -1, 4, 0), (true, -1, 3, 1), (true, -1, 2, 2), (false, -1, 2, 2), (false, 0, 2, 2), (false, 1, 2, 2), (true, 1, 2, 2), (true, 1, 1, 1), (true, 1, 0, 0), (false, 1, 0, 0), (false, 0, 0, 0)]

def word64 : Array P := #[1,2,0,0,2,0,2,1,2,1,2,1,2,0,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,0,2,1,2,0,2,0,2,1,1,2,1,2,0,2,0,2,0,2,1,2,1,1,2,0,0,2,1,1,2,1]

theorem step64 : ∀ i : Fin 64, push tab64[i.val]! word64[i.val]! = tab64[i.val+1]! := by decide +kernel

theorem closed64 : tab64[64]! = tab64[0]! := by decide +kernel

theorem chart64 : ∀ i j : Fin 64, i.val<j.val → separated tab64[i.val]! tab64[j.val]! ∨ mate i.val j.val := by decide +kernel

end Ribbon5Bridge
#print axioms Ribbon5Bridge.chart32
#print axioms Ribbon5Bridge.chart64
