import WeightData15Part0
namespace IU.IUW15
open IU.Eliminate
set_option maxRecDepth 15000
set_option maxHeartbeats 0
def p4_0 : Nat := 0x1
theorem p4_0_ok : pmask 4 0 = p4_0 := by
  rw [pmask]
  simp only [ite_true,p3_0_ok]
  decide +kernel
def p4_1 : Nat := 0x116
theorem p4_1_ok : pmask 4 1 = p4_1 := by
  rw [pmask]
  rw [if_neg (by decide),p3_1_ok,p3_0_ok]
  decide +kernel
def p4_2 : Nat := 0x1668
theorem p4_2_ok : pmask 4 2 = p4_2 := by
  rw [pmask]
  rw [if_neg (by decide),p3_2_ok,p3_1_ok]
  decide +kernel
def p4_3 : Nat := 0x6880
theorem p4_3_ok : pmask 4 3 = p4_3 := by
  rw [pmask]
  rw [if_neg (by decide),p3_3_ok,p3_2_ok]
  decide +kernel
def p4_4 : Nat := 0x8000
theorem p4_4_ok : pmask 4 4 = p4_4 := by
  rw [pmask]
  rw [if_neg (by decide),p3_3_ok]
  have Z : pmask 3 4=0 := pmask_above (by decide)
  rw [Z]
  decide +kernel
def p5_0 : Nat := 0x1
theorem p5_0_ok : pmask 5 0 = p5_0 := by
  rw [pmask]
  simp only [ite_true,p4_0_ok]
  decide +kernel
def p5_1 : Nat := 0x10116
theorem p5_1_ok : pmask 5 1 = p5_1 := by
  rw [pmask]
  rw [if_neg (by decide),p4_1_ok,p4_0_ok]
  decide +kernel
def p5_2 : Nat := 0x1161668
theorem p5_2_ok : pmask 5 2 = p5_2 := by
  rw [pmask]
  rw [if_neg (by decide),p4_2_ok,p4_1_ok]
  decide +kernel
def p5_3 : Nat := 0x16686880
theorem p5_3_ok : pmask 5 3 = p5_3 := by
  rw [pmask]
  rw [if_neg (by decide),p4_3_ok,p4_2_ok]
  decide +kernel
def p5_4 : Nat := 0x68808000
theorem p5_4_ok : pmask 5 4 = p5_4 := by
  rw [pmask]
  rw [if_neg (by decide),p4_4_ok,p4_3_ok]
  decide +kernel
def p5_5 : Nat := 0x80000000
theorem p5_5_ok : pmask 5 5 = p5_5 := by
  rw [pmask]
  rw [if_neg (by decide),p4_4_ok]
  have Z : pmask 4 5=0 := pmask_above (by decide)
  rw [Z]
  decide +kernel
def p6_0 : Nat := 0x1
theorem p6_0_ok : pmask 6 0 = p6_0 := by
  rw [pmask]
  simp only [ite_true,p5_0_ok]
  decide +kernel
def p6_1 : Nat := 0x100010116
theorem p6_1_ok : pmask 6 1 = p6_1 := by
  rw [pmask]
  rw [if_neg (by decide),p5_1_ok,p5_0_ok]
  decide +kernel
def p6_2 : Nat := 0x1011601161668
theorem p6_2_ok : pmask 6 2 = p6_2 := by
  rw [pmask]
  rw [if_neg (by decide),p5_2_ok,p5_1_ok]
  decide +kernel
def p6_3 : Nat := 0x116166816686880
theorem p6_3_ok : pmask 6 3 = p6_3 := by
  rw [pmask]
  rw [if_neg (by decide),p5_3_ok,p5_2_ok]
  decide +kernel
def p6_4 : Nat := 0x1668688068808000
theorem p6_4_ok : pmask 6 4 = p6_4 := by
  rw [pmask]
  rw [if_neg (by decide),p5_4_ok,p5_3_ok]
  decide +kernel
def p6_5 : Nat := 0x6880800080000000
theorem p6_5_ok : pmask 6 5 = p6_5 := by
  rw [pmask]
  rw [if_neg (by decide),p5_5_ok,p5_4_ok]
  decide +kernel
def p6_6 : Nat := 0x8000000000000000
theorem p6_6_ok : pmask 6 6 = p6_6 := by
  rw [pmask]
  rw [if_neg (by decide),p5_5_ok]
  have Z : pmask 5 6=0 := pmask_above (by decide)
  rw [Z]
  decide +kernel
def p7_0 : Nat := 0x1
theorem p7_0_ok : pmask 7 0 = p7_0 := by
  rw [pmask]
  simp only [ite_true,p6_0_ok]
  decide +kernel
def p7_1 : Nat := 0x10000000100010116
theorem p7_1_ok : pmask 7 1 = p7_1 := by
  rw [pmask]
  rw [if_neg (by decide),p6_1_ok,p6_0_ok]
  decide +kernel
def p7_2 : Nat := 0x1000101160001011601161668
theorem p7_2_ok : pmask 7 2 = p7_2 := by
  rw [pmask]
  rw [if_neg (by decide),p6_2_ok,p6_1_ok]
  decide +kernel
def p7_3 : Nat := 0x10116011616680116166816686880
theorem p7_3_ok : pmask 7 3 = p7_3 := by
  rw [pmask]
  rw [if_neg (by decide),p6_3_ok,p6_2_ok]
  decide +kernel
def p7_4 : Nat := 0x1161668166868801668688068808000
theorem p7_4_ok : pmask 7 4 = p7_4 := by
  rw [pmask]
  rw [if_neg (by decide),p6_4_ok,p6_3_ok]
  decide +kernel
def p7_5 : Nat := 0x16686880688080006880800080000000
theorem p7_5_ok : pmask 7 5 = p7_5 := by
  rw [pmask]
  rw [if_neg (by decide),p6_5_ok,p6_4_ok]
  decide +kernel
def p7_6 : Nat := 0x68808000800000008000000000000000
theorem p7_6_ok : pmask 7 6 = p7_6 := by
  rw [pmask]
  rw [if_neg (by decide),p6_6_ok,p6_5_ok]
  decide +kernel
def p7_7 : Nat := 0x80000000000000000000000000000000
theorem p7_7_ok : pmask 7 7 = p7_7 := by
  rw [pmask]
  rw [if_neg (by decide),p6_6_ok]
  have Z : pmask 6 7=0 := pmask_above (by decide)
  rw [Z]
  decide +kernel
end IU.IUW15
