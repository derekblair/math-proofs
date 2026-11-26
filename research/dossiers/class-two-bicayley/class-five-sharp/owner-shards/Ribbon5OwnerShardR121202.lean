import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R121202000 : good true 2 (pref true [2,1,2,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R121202002 : good true 2 (pref true [2,1,2,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R121202020 : good true 2 (pref true [2,1,2,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R121202021 : good true 2 (pref true [2,1,2,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R121202111 : good true 2 (pref true [2,1,2,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R121202112 : good true 2 (pref true [2,1,2,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R121202120 : good true 2 (pref true [2,1,2,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R121202121 : good true 2 (pref true [2,1,2,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R12120200 : good true 2 (pref true [2,1,2,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121202000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121202002
theorem R12120202 : good true 2 (pref true [2,1,2,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121202020
  · change good true 2 (step (pref true [2,1,2,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121202021
  · exact (hk (by decide)).elim
theorem R12120211 : good true 2 (pref true [2,1,2,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121202111
  · change good true 2 (step (pref true [2,1,2,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121202112
theorem R12120212 : good true 2 (pref true [2,1,2,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121202120
  · change good true 2 (step (pref true [2,1,2,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121202121
  · exact (hk (by decide)).elim
theorem R1212020 : good true 2 (pref true [2,1,2,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12120200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12120202
theorem R1212021 : good true 2 (pref true [2,1,2,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12120211
  · change good true 2 (step (pref true [2,1,2,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12120212
theorem R121202 : good true 2 (pref true [2,1,2,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1212020
  · change good true 2 (step (pref true [2,1,2,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1212021
  · exact (hk (by decide)).elim
end Ribbon5Owner
