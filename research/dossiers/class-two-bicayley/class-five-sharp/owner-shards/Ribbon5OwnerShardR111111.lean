import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R111111111 : good true 1 (pref true [1,1,1,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R111111112 : good true 1 (pref true [1,1,1,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R111111120 : good true 1 (pref true [1,1,1,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R111111121 : good true 1 (pref true [1,1,1,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R111111200 : good true 1 (pref true [1,1,1,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R111111202 : good true 1 (pref true [1,1,1,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R111111211 : good true 1 (pref true [1,1,1,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R111111212 : good true 1 (pref true [1,1,1,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R11111111 : good true 1 (pref true [1,1,1,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111111111
  · change good true 1 (step (pref true [1,1,1,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111111112
theorem R11111112 : good true 1 (pref true [1,1,1,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111111120
  · change good true 1 (step (pref true [1,1,1,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111111121
  · exact (hk (by decide)).elim
theorem R11111120 : good true 1 (pref true [1,1,1,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111111200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111111202
theorem R11111121 : good true 1 (pref true [1,1,1,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111111211
  · change good true 1 (step (pref true [1,1,1,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111111212
theorem R1111111 : good true 1 (pref true [1,1,1,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11111111
  · change good true 1 (step (pref true [1,1,1,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11111112
theorem R1111112 : good true 1 (pref true [1,1,1,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11111120
  · change good true 1 (step (pref true [1,1,1,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11111121
  · exact (hk (by decide)).elim
theorem R111111 : good true 1 (pref true [1,1,1,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1111111
  · change good true 1 (step (pref true [1,1,1,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1111112
end Ribbon5Owner
