import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R102120000 : good true 0 (pref true [0,2,1,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R102120002 : good true 0 (pref true [0,2,1,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R102120020 : good true 0 (pref true [0,2,1,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R102120021 : good true 0 (pref true [0,2,1,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R102120200 : good true 0 (pref true [0,2,1,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R102120202 : good true 0 (pref true [0,2,1,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R102120211 : good true 0 (pref true [0,2,1,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R102120212 : good true 0 (pref true [0,2,1,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R10212000 : good true 0 (pref true [0,2,1,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102120000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102120002
theorem R10212002 : good true 0 (pref true [0,2,1,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102120020
  · change good true 0 (step (pref true [0,2,1,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102120021
  · exact (hk (by decide)).elim
theorem R10212020 : good true 0 (pref true [0,2,1,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102120200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102120202
theorem R10212021 : good true 0 (pref true [0,2,1,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102120211
  · change good true 0 (step (pref true [0,2,1,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102120212
theorem R1021200 : good true 0 (pref true [0,2,1,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10212000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10212002
theorem R1021202 : good true 0 (pref true [0,2,1,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10212020
  · change good true 0 (step (pref true [0,2,1,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10212021
  · exact (hk (by decide)).elim
theorem R102120 : good true 0 (pref true [0,2,1,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1021200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1021202
end Ribbon5Owner
