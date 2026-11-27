import WeightMasks
namespace IU.IUW15
open IU.Eliminate
set_option maxRecDepth 15000
set_option maxHeartbeats 0
def p0_0 : Nat := 0x1
theorem p0_0_ok : pmask 0 0 = p0_0 := by
  rfl
def p1_0 : Nat := 0x1
theorem p1_0_ok : pmask 1 0 = p1_0 := by
  rw [pmask]
  simp only [ite_true,p0_0_ok]
  decide +kernel
def p1_1 : Nat := 0x2
theorem p1_1_ok : pmask 1 1 = p1_1 := by
  rw [pmask]
  rw [if_neg (by decide),p0_0_ok]
  have Z : pmask 0 1=0 := pmask_above (by decide)
  rw [Z]
  decide +kernel
def p2_0 : Nat := 0x1
theorem p2_0_ok : pmask 2 0 = p2_0 := by
  rw [pmask]
  simp only [ite_true,p1_0_ok]
  decide +kernel
def p2_1 : Nat := 0x6
theorem p2_1_ok : pmask 2 1 = p2_1 := by
  rw [pmask]
  rw [if_neg (by decide),p1_1_ok,p1_0_ok]
  decide +kernel
def p2_2 : Nat := 0x8
theorem p2_2_ok : pmask 2 2 = p2_2 := by
  rw [pmask]
  rw [if_neg (by decide),p1_1_ok]
  have Z : pmask 1 2=0 := pmask_above (by decide)
  rw [Z]
  decide +kernel
def p3_0 : Nat := 0x1
theorem p3_0_ok : pmask 3 0 = p3_0 := by
  rw [pmask]
  simp only [ite_true,p2_0_ok]
  decide +kernel
def p3_1 : Nat := 0x16
theorem p3_1_ok : pmask 3 1 = p3_1 := by
  rw [pmask]
  rw [if_neg (by decide),p2_1_ok,p2_0_ok]
  decide +kernel
def p3_2 : Nat := 0x68
theorem p3_2_ok : pmask 3 2 = p3_2 := by
  rw [pmask]
  rw [if_neg (by decide),p2_2_ok,p2_1_ok]
  decide +kernel
def p3_3 : Nat := 0x80
theorem p3_3_ok : pmask 3 3 = p3_3 := by
  rw [pmask]
  rw [if_neg (by decide),p2_2_ok]
  have Z : pmask 2 3=0 := pmask_above (by decide)
  rw [Z]
  decide +kernel
end IU.IUW15
