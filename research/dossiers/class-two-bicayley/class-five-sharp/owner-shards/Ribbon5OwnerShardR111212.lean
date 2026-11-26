import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R111212000 : good true 1 (pref true [1,1,2,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R111212002 : good true 1 (pref true [1,1,2,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R111212020 : good true 1 (pref true [1,1,2,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R111212021 : good true 1 (pref true [1,1,2,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R111212111 : good true 1 (pref true [1,1,2,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R111212112 : good true 1 (pref true [1,1,2,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R111212120 : good true 1 (pref true [1,1,2,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R111212121 : good true 1 (pref true [1,1,2,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R11121200 : good true 1 (pref true [1,1,2,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111212000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111212002
theorem R11121202 : good true 1 (pref true [1,1,2,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111212020
  · change good true 1 (step (pref true [1,1,2,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111212021
  · exact (hk (by decide)).elim
theorem R11121211 : good true 1 (pref true [1,1,2,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111212111
  · change good true 1 (step (pref true [1,1,2,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111212112
theorem R11121212 : good true 1 (pref true [1,1,2,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111212120
  · change good true 1 (step (pref true [1,1,2,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111212121
  · exact (hk (by decide)).elim
theorem R1112120 : good true 1 (pref true [1,1,2,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11121200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11121202
theorem R1112121 : good true 1 (pref true [1,1,2,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11121211
  · change good true 1 (step (pref true [1,1,2,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11121212
theorem R111212 : good true 1 (pref true [1,1,2,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1112120
  · change good true 1 (step (pref true [1,1,2,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1112121
  · exact (hk (by decide)).elim
end Ribbon5Owner
