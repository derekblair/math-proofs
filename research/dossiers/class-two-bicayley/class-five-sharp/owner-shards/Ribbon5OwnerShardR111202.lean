import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R111202000 : good true 1 (pref true [1,1,2,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R111202002 : good true 1 (pref true [1,1,2,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R111202020 : good true 1 (pref true [1,1,2,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R111202021 : good true 1 (pref true [1,1,2,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R111202111 : good true 1 (pref true [1,1,2,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R111202112 : good true 1 (pref true [1,1,2,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R111202120 : good true 1 (pref true [1,1,2,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R111202121 : good true 1 (pref true [1,1,2,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R11120200 : good true 1 (pref true [1,1,2,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111202000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111202002
theorem R11120202 : good true 1 (pref true [1,1,2,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111202020
  · change good true 1 (step (pref true [1,1,2,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111202021
  · exact (hk (by decide)).elim
theorem R11120211 : good true 1 (pref true [1,1,2,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111202111
  · change good true 1 (step (pref true [1,1,2,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111202112
theorem R11120212 : good true 1 (pref true [1,1,2,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111202120
  · change good true 1 (step (pref true [1,1,2,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111202121
  · exact (hk (by decide)).elim
theorem R1112020 : good true 1 (pref true [1,1,2,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11120200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11120202
theorem R1112021 : good true 1 (pref true [1,1,2,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11120211
  · change good true 1 (step (pref true [1,1,2,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11120212
theorem R111202 : good true 1 (pref true [1,1,2,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1112020
  · change good true 1 (step (pref true [1,1,2,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1112021
  · exact (hk (by decide)).elim
end Ribbon5Owner
