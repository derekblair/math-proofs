import N63TableCore
import Mathlib.Tactic.IntervalCases

namespace Erdos151N63
set_option maxHeartbeats 0

def minCenter (d y : Nat) : Nat :=
  match d,y with
  | 3,3 => 3
  | 4,3 | 5,3 => 2
  | 4,4 | 5,4 | 5,5 | 6,3 | 7,3 => 1
  | 6,4 | 6,5 | 6,6 | 7,4 | 7,5 | 7,6 | 7,7 | 8,3 | 8,4 | 8,5 | 8,6 | 8,7 | 8,8 => 0
  | _,_ => 99

theorem minCenter_kernel : ∀ x y : Fin 9, minCenter x.val y.val ≠ 99 →
    priceOK 10 x.val y.val (minCenter x.val y.val) := by decide +kernel

theorem minCenter_sound (x y m : Nat) (hx : x ≤ 8) (hy : y ≤ 8)
    (known : minCenter x y ≠ 99) (hm : minCenter x y ≤ m) :
    priceOK 10 x y m := by
  intro i j s
  have h := minCenter_kernel ⟨x,by omega⟩ ⟨y,by omega⟩ known i j s
  change 17 ≤ 4 + (x+i.val) + (y+j.val) + s.val + minCenter x y +
    outerFloor (x+i.val) (y+j.val) s.val at h
  omega

#print axioms minCenter_sound
end Erdos151N63
