import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R111120000 : good true 1 (pref true [1,1,1,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R111120002 : good true 1 (pref true [1,1,1,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R111120020 : good true 1 (pref true [1,1,1,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R111120021 : good true 1 (pref true [1,1,1,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R111120200 : good true 1 (pref true [1,1,1,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R111120202 : good true 1 (pref true [1,1,1,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R111120211 : good true 1 (pref true [1,1,1,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R111120212 : good true 1 (pref true [1,1,1,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R11112000 : good true 1 (pref true [1,1,1,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111120000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111120002
theorem R11112002 : good true 1 (pref true [1,1,1,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111120020
  · change good true 1 (step (pref true [1,1,1,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111120021
  · exact (hk (by decide)).elim
theorem R11112020 : good true 1 (pref true [1,1,1,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111120200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111120202
theorem R11112021 : good true 1 (pref true [1,1,1,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111120211
  · change good true 1 (step (pref true [1,1,1,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111120212
theorem R1111200 : good true 1 (pref true [1,1,1,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11112000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11112002
theorem R1111202 : good true 1 (pref true [1,1,1,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11112020
  · change good true 1 (step (pref true [1,1,1,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11112021
  · exact (hk (by decide)).elim
theorem R111120 : good true 1 (pref true [1,1,1,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1111200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1111202
end Ribbon5Owner
