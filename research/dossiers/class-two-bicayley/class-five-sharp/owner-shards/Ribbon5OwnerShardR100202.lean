import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R100202000 : good true 0 (pref true [0,0,2,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R100202002 : good true 0 (pref true [0,0,2,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R100202020 : good true 0 (pref true [0,0,2,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R100202021 : good true 0 (pref true [0,0,2,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R100202111 : good true 0 (pref true [0,0,2,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R100202112 : good true 0 (pref true [0,0,2,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R100202120 : good true 0 (pref true [0,0,2,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R100202121 : good true 0 (pref true [0,0,2,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R10020200 : good true 0 (pref true [0,0,2,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100202000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100202002
theorem R10020202 : good true 0 (pref true [0,0,2,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100202020
  · change good true 0 (step (pref true [0,0,2,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100202021
  · exact (hk (by decide)).elim
theorem R10020211 : good true 0 (pref true [0,0,2,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100202111
  · change good true 0 (step (pref true [0,0,2,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100202112
theorem R10020212 : good true 0 (pref true [0,0,2,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100202120
  · change good true 0 (step (pref true [0,0,2,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100202121
  · exact (hk (by decide)).elim
theorem R1002020 : good true 0 (pref true [0,0,2,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10020200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10020202
theorem R1002021 : good true 0 (pref true [0,0,2,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10020211
  · change good true 0 (step (pref true [0,0,2,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10020212
theorem R100202 : good true 0 (pref true [0,0,2,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1002020
  · change good true 0 (step (pref true [0,0,2,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1002021
  · exact (hk (by decide)).elim
end Ribbon5Owner
