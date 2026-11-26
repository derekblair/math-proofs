import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R120211111 : good true 2 (pref true [2,0,2,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R120211112 : good true 2 (pref true [2,0,2,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R120211120 : good true 2 (pref true [2,0,2,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R120211121 : good true 2 (pref true [2,0,2,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R120211200 : good true 2 (pref true [2,0,2,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R120211202 : good true 2 (pref true [2,0,2,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R120211211 : good true 2 (pref true [2,0,2,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R120211212 : good true 2 (pref true [2,0,2,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R12021111 : good true 2 (pref true [2,0,2,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120211111
  · change good true 2 (step (pref true [2,0,2,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120211112
theorem R12021112 : good true 2 (pref true [2,0,2,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120211120
  · change good true 2 (step (pref true [2,0,2,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120211121
  · exact (hk (by decide)).elim
theorem R12021120 : good true 2 (pref true [2,0,2,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120211200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120211202
theorem R12021121 : good true 2 (pref true [2,0,2,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120211211
  · change good true 2 (step (pref true [2,0,2,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120211212
theorem R1202111 : good true 2 (pref true [2,0,2,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12021111
  · change good true 2 (step (pref true [2,0,2,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12021112
theorem R1202112 : good true 2 (pref true [2,0,2,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12021120
  · change good true 2 (step (pref true [2,0,2,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12021121
  · exact (hk (by decide)).elim
theorem R120211 : good true 2 (pref true [2,0,2,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1202111
  · change good true 2 (step (pref true [2,0,2,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1202112
end Ribbon5Owner
