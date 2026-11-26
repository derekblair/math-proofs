import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R102121111 : good true 0 (pref true [0,2,1,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R102121112 : good true 0 (pref true [0,2,1,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R102121120 : good true 0 (pref true [0,2,1,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R102121121 : good true 0 (pref true [0,2,1,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R102121200 : good true 0 (pref true [0,2,1,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R102121202 : good true 0 (pref true [0,2,1,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R102121211 : good true 0 (pref true [0,2,1,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R102121212 : good true 0 (pref true [0,2,1,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R10212111 : good true 0 (pref true [0,2,1,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102121111
  · change good true 0 (step (pref true [0,2,1,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102121112
theorem R10212112 : good true 0 (pref true [0,2,1,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102121120
  · change good true 0 (step (pref true [0,2,1,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102121121
  · exact (hk (by decide)).elim
theorem R10212120 : good true 0 (pref true [0,2,1,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102121200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102121202
theorem R10212121 : good true 0 (pref true [0,2,1,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102121211
  · change good true 0 (step (pref true [0,2,1,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102121212
theorem R1021211 : good true 0 (pref true [0,2,1,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10212111
  · change good true 0 (step (pref true [0,2,1,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10212112
theorem R1021212 : good true 0 (pref true [0,2,1,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10212120
  · change good true 0 (step (pref true [0,2,1,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10212121
  · exact (hk (by decide)).elim
theorem R102121 : good true 0 (pref true [0,2,1,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1021211
  · change good true 0 (step (pref true [0,2,1,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1021212
end Ribbon5Owner
