import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R121212000 : good true 2 (pref true [2,1,2,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R121212002 : good true 2 (pref true [2,1,2,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R121212020 : good true 2 (pref true [2,1,2,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R121212021 : good true 2 (pref true [2,1,2,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R121212111 : good true 2 (pref true [2,1,2,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R121212112 : good true 2 (pref true [2,1,2,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R121212120 : good true 2 (pref true [2,1,2,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R121212121 : good true 2 (pref true [2,1,2,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R12121200 : good true 2 (pref true [2,1,2,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121212000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121212002
theorem R12121202 : good true 2 (pref true [2,1,2,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121212020
  · change good true 2 (step (pref true [2,1,2,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121212021
  · exact (hk (by decide)).elim
theorem R12121211 : good true 2 (pref true [2,1,2,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121212111
  · change good true 2 (step (pref true [2,1,2,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121212112
theorem R12121212 : good true 2 (pref true [2,1,2,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121212120
  · change good true 2 (step (pref true [2,1,2,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121212121
  · exact (hk (by decide)).elim
theorem R1212120 : good true 2 (pref true [2,1,2,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12121200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12121202
theorem R1212121 : good true 2 (pref true [2,1,2,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12121211
  · change good true 2 (step (pref true [2,1,2,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12121212
theorem R121212 : good true 2 (pref true [2,1,2,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1212120
  · change good true 2 (step (pref true [2,1,2,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1212121
  · exact (hk (by decide)).elim
end Ribbon5Owner
