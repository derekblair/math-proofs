import WeightData15Part3
import Mathlib.Tactic.FinCases
namespace IU.IUW15
open IU.Eliminate
set_option maxRecDepth 15000
set_option maxHeartbeats 0
def T0 : Array Nat := #[p0_0]
theorem T0_ok (k : Fin 1) : T0[k.val]! = pmask 0 k.val := by
  fin_cases k
  · exact p0_0_ok.symm
def T1 : Array Nat := #[p1_0,p1_1]
theorem T1_ok (k : Fin 2) : T1[k.val]! = pmask 1 k.val := by
  fin_cases k
  · exact p1_0_ok.symm
  · exact p1_1_ok.symm
def T2 : Array Nat := #[p2_0,p2_1,p2_2]
theorem T2_ok (k : Fin 3) : T2[k.val]! = pmask 2 k.val := by
  fin_cases k
  · exact p2_0_ok.symm
  · exact p2_1_ok.symm
  · exact p2_2_ok.symm
def T3 : Array Nat := #[p3_0,p3_1,p3_2,p3_3]
theorem T3_ok (k : Fin 4) : T3[k.val]! = pmask 3 k.val := by
  fin_cases k
  · exact p3_0_ok.symm
  · exact p3_1_ok.symm
  · exact p3_2_ok.symm
  · exact p3_3_ok.symm
def T4 : Array Nat := #[p4_0,p4_1,p4_2,p4_3,p4_4]
theorem T4_ok (k : Fin 5) : T4[k.val]! = pmask 4 k.val := by
  fin_cases k
  · exact p4_0_ok.symm
  · exact p4_1_ok.symm
  · exact p4_2_ok.symm
  · exact p4_3_ok.symm
  · exact p4_4_ok.symm
def T5 : Array Nat := #[p5_0,p5_1,p5_2,p5_3,p5_4,p5_5]
theorem T5_ok (k : Fin 6) : T5[k.val]! = pmask 5 k.val := by
  fin_cases k
  · exact p5_0_ok.symm
  · exact p5_1_ok.symm
  · exact p5_2_ok.symm
  · exact p5_3_ok.symm
  · exact p5_4_ok.symm
  · exact p5_5_ok.symm
def T6 : Array Nat := #[p6_0,p6_1,p6_2,p6_3,p6_4,p6_5,p6_6]
theorem T6_ok (k : Fin 7) : T6[k.val]! = pmask 6 k.val := by
  fin_cases k
  · exact p6_0_ok.symm
  · exact p6_1_ok.symm
  · exact p6_2_ok.symm
  · exact p6_3_ok.symm
  · exact p6_4_ok.symm
  · exact p6_5_ok.symm
  · exact p6_6_ok.symm
def T7 : Array Nat := #[p7_0,p7_1,p7_2,p7_3,p7_4,p7_5,p7_6,p7_7]
theorem T7_ok (k : Fin 8) : T7[k.val]! = pmask 7 k.val := by
  fin_cases k
  · exact p7_0_ok.symm
  · exact p7_1_ok.symm
  · exact p7_2_ok.symm
  · exact p7_3_ok.symm
  · exact p7_4_ok.symm
  · exact p7_5_ok.symm
  · exact p7_6_ok.symm
  · exact p7_7_ok.symm
def T8 : Array Nat := #[p8_0,p8_1,p8_2,p8_3,p8_4,p8_5,p8_6,p8_7,p8_8]
theorem T8_ok (k : Fin 9) : T8[k.val]! = pmask 8 k.val := by
  fin_cases k
  · exact p8_0_ok.symm
  · exact p8_1_ok.symm
  · exact p8_2_ok.symm
  · exact p8_3_ok.symm
  · exact p8_4_ok.symm
  · exact p8_5_ok.symm
  · exact p8_6_ok.symm
  · exact p8_7_ok.symm
  · exact p8_8_ok.symm
def T9 : Array Nat := #[p9_0,p9_1,p9_2,p9_3,p9_4,p9_5,p9_6,p9_7,p9_8,p9_9]
theorem T9_ok (k : Fin 10) : T9[k.val]! = pmask 9 k.val := by
  fin_cases k
  · exact p9_0_ok.symm
  · exact p9_1_ok.symm
  · exact p9_2_ok.symm
  · exact p9_3_ok.symm
  · exact p9_4_ok.symm
  · exact p9_5_ok.symm
  · exact p9_6_ok.symm
  · exact p9_7_ok.symm
  · exact p9_8_ok.symm
  · exact p9_9_ok.symm
def T10 : Array Nat := #[p10_0,p10_1,p10_2,p10_3,p10_4,p10_5,p10_6,p10_7,p10_8,p10_9,p10_10]
theorem T10_ok (k : Fin 11) : T10[k.val]! = pmask 10 k.val := by
  fin_cases k
  · exact p10_0_ok.symm
  · exact p10_1_ok.symm
  · exact p10_2_ok.symm
  · exact p10_3_ok.symm
  · exact p10_4_ok.symm
  · exact p10_5_ok.symm
  · exact p10_6_ok.symm
  · exact p10_7_ok.symm
  · exact p10_8_ok.symm
  · exact p10_9_ok.symm
  · exact p10_10_ok.symm
def T11 : Array Nat := #[p11_0,p11_1,p11_2,p11_3,p11_4,p11_5,p11_6,p11_7,p11_8,p11_9,p11_10,p11_11]
theorem T11_ok (k : Fin 12) : T11[k.val]! = pmask 11 k.val := by
  fin_cases k
  · exact p11_0_ok.symm
  · exact p11_1_ok.symm
  · exact p11_2_ok.symm
  · exact p11_3_ok.symm
  · exact p11_4_ok.symm
  · exact p11_5_ok.symm
  · exact p11_6_ok.symm
  · exact p11_7_ok.symm
  · exact p11_8_ok.symm
  · exact p11_9_ok.symm
  · exact p11_10_ok.symm
  · exact p11_11_ok.symm
def T12 : Array Nat := #[p12_0,p12_1,p12_2,p12_3,p12_4,p12_5,p12_6,p12_7,p12_8,p12_9,p12_10,p12_11,p12_12]
theorem T12_ok (k : Fin 13) : T12[k.val]! = pmask 12 k.val := by
  fin_cases k
  · exact p12_0_ok.symm
  · exact p12_1_ok.symm
  · exact p12_2_ok.symm
  · exact p12_3_ok.symm
  · exact p12_4_ok.symm
  · exact p12_5_ok.symm
  · exact p12_6_ok.symm
  · exact p12_7_ok.symm
  · exact p12_8_ok.symm
  · exact p12_9_ok.symm
  · exact p12_10_ok.symm
  · exact p12_11_ok.symm
  · exact p12_12_ok.symm
def T13 : Array Nat := #[p13_0,p13_1,p13_2,p13_3,p13_4,p13_5,p13_6,p13_7,p13_8,p13_9,p13_10,p13_11,p13_12,p13_13]
theorem T13_ok (k : Fin 14) : T13[k.val]! = pmask 13 k.val := by
  fin_cases k
  · exact p13_0_ok.symm
  · exact p13_1_ok.symm
  · exact p13_2_ok.symm
  · exact p13_3_ok.symm
  · exact p13_4_ok.symm
  · exact p13_5_ok.symm
  · exact p13_6_ok.symm
  · exact p13_7_ok.symm
  · exact p13_8_ok.symm
  · exact p13_9_ok.symm
  · exact p13_10_ok.symm
  · exact p13_11_ok.symm
  · exact p13_12_ok.symm
  · exact p13_13_ok.symm
def T14 : Array Nat := #[p14_0,p14_1,p14_2,p14_3,p14_4,p14_5,p14_6,p14_7,p14_8,p14_9,p14_10,p14_11,p14_12,p14_13,p14_14]
theorem T14_ok (k : Fin 15) : T14[k.val]! = pmask 14 k.val := by
  fin_cases k
  · exact p14_0_ok.symm
  · exact p14_1_ok.symm
  · exact p14_2_ok.symm
  · exact p14_3_ok.symm
  · exact p14_4_ok.symm
  · exact p14_5_ok.symm
  · exact p14_6_ok.symm
  · exact p14_7_ok.symm
  · exact p14_8_ok.symm
  · exact p14_9_ok.symm
  · exact p14_10_ok.symm
  · exact p14_11_ok.symm
  · exact p14_12_ok.symm
  · exact p14_13_ok.symm
  · exact p14_14_ok.symm
def T15 : Array Nat := #[p15_0,p15_1,p15_2,p15_3,p15_4,p15_5,p15_6,p15_7,p15_8,p15_9,p15_10,p15_11,p15_12,p15_13,p15_14,p15_15]
theorem T15_ok (k : Fin 16) : T15[k.val]! = pmask 15 k.val := by
  fin_cases k
  · exact p15_0_ok.symm
  · exact p15_1_ok.symm
  · exact p15_2_ok.symm
  · exact p15_3_ok.symm
  · exact p15_4_ok.symm
  · exact p15_5_ok.symm
  · exact p15_6_ok.symm
  · exact p15_7_ok.symm
  · exact p15_8_ok.symm
  · exact p15_9_ok.symm
  · exact p15_10_ok.symm
  · exact p15_11_ok.symm
  · exact p15_12_ok.symm
  · exact p15_13_ok.symm
  · exact p15_14_ok.symm
  · exact p15_15_ok.symm
def tab (t k : Nat) : Nat := match t with
  | 0 => T0[k]!
  | 1 => T1[k]!
  | 2 => T2[k]!
  | 3 => T3[k]!
  | 4 => T4[k]!
  | 5 => T5[k]!
  | 6 => T6[k]!
  | 7 => T7[k]!
  | 8 => T8[k]!
  | 9 => T9[k]!
  | 10 => T10[k]!
  | 11 => T11[k]!
  | 12 => T12[k]!
  | 13 => T13[k]!
  | 14 => T14[k]!
  | 15 => T15[k]!
  | _ => 0
theorem tab_ok (t : Nat) (h : t≤15) (k : Nat) (hk : k≤t) : tab t k=pmask t k := by
  let i : Fin 16 := ⟨t,by omega⟩
  change k≤i.val at hk
  change tab i.val k=pmask i.val k
  clear_value i
  fin_cases i
  · exact T0_ok ⟨k,by dsimp at hk; omega⟩
  · exact T1_ok ⟨k,by dsimp at hk; omega⟩
  · exact T2_ok ⟨k,by dsimp at hk; omega⟩
  · exact T3_ok ⟨k,by dsimp at hk; omega⟩
  · exact T4_ok ⟨k,by dsimp at hk; omega⟩
  · exact T5_ok ⟨k,by dsimp at hk; omega⟩
  · exact T6_ok ⟨k,by dsimp at hk; omega⟩
  · exact T7_ok ⟨k,by dsimp at hk; omega⟩
  · exact T8_ok ⟨k,by dsimp at hk; omega⟩
  · exact T9_ok ⟨k,by dsimp at hk; omega⟩
  · exact T10_ok ⟨k,by dsimp at hk; omega⟩
  · exact T11_ok ⟨k,by dsimp at hk; omega⟩
  · exact T12_ok ⟨k,by dsimp at hk; omega⟩
  · exact T13_ok ⟨k,by dsimp at hk; omega⟩
  · exact T14_ok ⟨k,by dsimp at hk; omega⟩
  · exact T15_ok ⟨k,by dsimp at hk; omega⟩
end IU.IUW15
