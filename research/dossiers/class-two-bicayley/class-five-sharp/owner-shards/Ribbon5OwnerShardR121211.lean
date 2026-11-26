import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R121211111 : good true 2 (pref true [2,1,2,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R121211112 : good true 2 (pref true [2,1,2,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R121211120 : good true 2 (pref true [2,1,2,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R121211121 : good true 2 (pref true [2,1,2,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R121211200 : good true 2 (pref true [2,1,2,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R121211202 : good true 2 (pref true [2,1,2,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R121211211 : good true 2 (pref true [2,1,2,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R121211212 : good true 2 (pref true [2,1,2,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R12121111 : good true 2 (pref true [2,1,2,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121211111
  · change good true 2 (step (pref true [2,1,2,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121211112
theorem R12121112 : good true 2 (pref true [2,1,2,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121211120
  · change good true 2 (step (pref true [2,1,2,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121211121
  · exact (hk (by decide)).elim
theorem R12121120 : good true 2 (pref true [2,1,2,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121211200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121211202
theorem R12121121 : good true 2 (pref true [2,1,2,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121211211
  · change good true 2 (step (pref true [2,1,2,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121211212
theorem R1212111 : good true 2 (pref true [2,1,2,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12121111
  · change good true 2 (step (pref true [2,1,2,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12121112
theorem R1212112 : good true 2 (pref true [2,1,2,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12121120
  · change good true 2 (step (pref true [2,1,2,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12121121
  · exact (hk (by decide)).elim
theorem R121211 : good true 2 (pref true [2,1,2,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1212111
  · change good true 2 (step (pref true [2,1,2,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1212112
end Ribbon5Owner
