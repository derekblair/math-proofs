import Mathlib.Tactic.IntervalCases
import N63Code4_00
import N63Code4_08
import N63Code4_16
import N63Code4_24
import N63Code4_32
import N63Code4_40
import N63Code4_48
import N63Code4_56
import N63Code5_00
import N63Code6_00
import N63Code7_00
import N63Code8_00
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem bind_all_codes (d h : Nat) (hd : 4 ≤ d) (hd2 : d ≤ 8)
    (hh : h < 2^((8-d)*(7-d)/2)) (r : Array Nat) (hr : r ∈ enumFast 9 14 d h) :
    ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  have hdv : d=4 ∨ d=5 ∨ d=6 ∨ d=7 ∨ d=8 := by omega
  rcases hdv with rfl | rfl | rfl | rfl | rfl
  · change h < 64 at hh
    interval_cases h
    · exact bind4_0 r hr
    · exact bind4_1 r hr
    · exact bind4_2 r hr
    · exact bind4_3 r hr
    · exact bind4_4 r hr
    · exact bind4_5 r hr
    · exact bind4_6 r hr
    · exact bind4_7 r hr
    · exact bind4_8 r hr
    · exact bind4_9 r hr
    · exact bind4_10 r hr
    · exact bind4_11 r hr
    · exact bind4_12 r hr
    · exact bind4_13 r hr
    · exact bind4_14 r hr
    · exact bind4_15 r hr
    · exact bind4_16 r hr
    · exact bind4_17 r hr
    · exact bind4_18 r hr
    · exact bind4_19 r hr
    · exact bind4_20 r hr
    · exact bind4_21 r hr
    · exact bind4_22 r hr
    · exact bind4_23 r hr
    · exact bind4_24 r hr
    · exact bind4_25 r hr
    · exact bind4_26 r hr
    · exact bind4_27 r hr
    · exact bind4_28 r hr
    · exact bind4_29 r hr
    · exact bind4_30 r hr
    · exact bind4_31 r hr
    · exact bind4_32 r hr
    · exact bind4_33 r hr
    · exact bind4_34 r hr
    · exact bind4_35 r hr
    · exact bind4_36 r hr
    · exact bind4_37 r hr
    · exact bind4_38 r hr
    · exact bind4_39 r hr
    · exact bind4_40 r hr
    · exact bind4_41 r hr
    · exact bind4_42 r hr
    · exact bind4_43 r hr
    · exact bind4_44 r hr
    · exact bind4_45 r hr
    · exact bind4_46 r hr
    · exact bind4_47 r hr
    · exact bind4_48 r hr
    · exact bind4_49 r hr
    · exact bind4_50 r hr
    · exact bind4_51 r hr
    · exact bind4_52 r hr
    · exact bind4_53 r hr
    · exact bind4_54 r hr
    · exact bind4_55 r hr
    · exact bind4_56 r hr
    · exact bind4_57 r hr
    · exact bind4_58 r hr
    · exact bind4_59 r hr
    · exact bind4_60 r hr
    · exact bind4_61 r hr
    · exact bind4_62 r hr
    · exact bind4_63 r hr
  · change h < 8 at hh
    interval_cases h
    · exact bind5_0 r hr
    · exact bind5_1 r hr
    · exact bind5_2 r hr
    · exact bind5_3 r hr
    · exact bind5_4 r hr
    · exact bind5_5 r hr
    · exact bind5_6 r hr
    · exact bind5_7 r hr
  · change h < 2 at hh
    interval_cases h
    · exact bind6_0 r hr
    · exact bind6_1 r hr
  · change h < 1 at hh
    have eq : h=0 := by omega
    subst h
    exact bind7_0 r hr
  · change h < 1 at hh
    have eq : h=0 := by omega
    subst h
    exact bind8_0 r hr
#print axioms bind_all_codes
end Erdos151N63
