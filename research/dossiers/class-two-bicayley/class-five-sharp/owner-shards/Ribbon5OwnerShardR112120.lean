import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R112120000 : good true 1 (pref true [1,2,1,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R112120002 : good true 1 (pref true [1,2,1,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R112120020 : good true 1 (pref true [1,2,1,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R112120021 : good true 1 (pref true [1,2,1,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R112120200 : good true 1 (pref true [1,2,1,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R112120202 : good true 1 (pref true [1,2,1,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R112120211 : good true 1 (pref true [1,2,1,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R112120212 : good true 1 (pref true [1,2,1,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R11212000 : good true 1 (pref true [1,2,1,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112120000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112120002
theorem R11212002 : good true 1 (pref true [1,2,1,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112120020
  · change good true 1 (step (pref true [1,2,1,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112120021
  · exact (hk (by decide)).elim
theorem R11212020 : good true 1 (pref true [1,2,1,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112120200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112120202
theorem R11212021 : good true 1 (pref true [1,2,1,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112120211
  · change good true 1 (step (pref true [1,2,1,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112120212
theorem R1121200 : good true 1 (pref true [1,2,1,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11212000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11212002
theorem R1121202 : good true 1 (pref true [1,2,1,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11212020
  · change good true 1 (step (pref true [1,2,1,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11212021
  · exact (hk (by decide)).elim
theorem R112120 : good true 1 (pref true [1,2,1,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1121200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1121202
end Ribbon5Owner
