import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R111112000 : good true 1 (pref true [1,1,1,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R111112002 : good true 1 (pref true [1,1,1,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R111112020 : good true 1 (pref true [1,1,1,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R111112021 : good true 1 (pref true [1,1,1,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R111112111 : good true 1 (pref true [1,1,1,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R111112112 : good true 1 (pref true [1,1,1,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R111112120 : good true 1 (pref true [1,1,1,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R111112121 : good true 1 (pref true [1,1,1,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R11111200 : good true 1 (pref true [1,1,1,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111112000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111112002
theorem R11111202 : good true 1 (pref true [1,1,1,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111112020
  · change good true 1 (step (pref true [1,1,1,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111112021
  · exact (hk (by decide)).elim
theorem R11111211 : good true 1 (pref true [1,1,1,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111112111
  · change good true 1 (step (pref true [1,1,1,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111112112
theorem R11111212 : good true 1 (pref true [1,1,1,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111112120
  · change good true 1 (step (pref true [1,1,1,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111112121
  · exact (hk (by decide)).elim
theorem R1111120 : good true 1 (pref true [1,1,1,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11111200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11111202
theorem R1111121 : good true 1 (pref true [1,1,1,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11111211
  · change good true 1 (step (pref true [1,1,1,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11111212
theorem R111112 : good true 1 (pref true [1,1,1,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1111120
  · change good true 1 (step (pref true [1,1,1,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1111121
  · exact (hk (by decide)).elim
end Ribbon5Owner
