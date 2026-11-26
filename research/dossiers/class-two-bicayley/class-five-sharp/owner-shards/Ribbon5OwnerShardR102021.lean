import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R102021111 : good true 0 (pref true [0,2,0,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R102021112 : good true 0 (pref true [0,2,0,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R102021120 : good true 0 (pref true [0,2,0,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R102021121 : good true 0 (pref true [0,2,0,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R102021200 : good true 0 (pref true [0,2,0,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R102021202 : good true 0 (pref true [0,2,0,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R102021211 : good true 0 (pref true [0,2,0,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R102021212 : good true 0 (pref true [0,2,0,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R10202111 : good true 0 (pref true [0,2,0,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102021111
  · change good true 0 (step (pref true [0,2,0,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102021112
theorem R10202112 : good true 0 (pref true [0,2,0,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102021120
  · change good true 0 (step (pref true [0,2,0,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102021121
  · exact (hk (by decide)).elim
theorem R10202120 : good true 0 (pref true [0,2,0,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102021200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102021202
theorem R10202121 : good true 0 (pref true [0,2,0,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102021211
  · change good true 0 (step (pref true [0,2,0,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102021212
theorem R1020211 : good true 0 (pref true [0,2,0,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10202111
  · change good true 0 (step (pref true [0,2,0,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10202112
theorem R1020212 : good true 0 (pref true [0,2,0,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10202120
  · change good true 0 (step (pref true [0,2,0,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10202121
  · exact (hk (by decide)).elim
theorem R102021 : good true 0 (pref true [0,2,0,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1020211
  · change good true 0 (step (pref true [0,2,0,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1020212
end Ribbon5Owner
