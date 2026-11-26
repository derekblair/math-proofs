import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R111121111 : good true 1 (pref true [1,1,1,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R111121112 : good true 1 (pref true [1,1,1,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R111121120 : good true 1 (pref true [1,1,1,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R111121121 : good true 1 (pref true [1,1,1,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R111121200 : good true 1 (pref true [1,1,1,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R111121202 : good true 1 (pref true [1,1,1,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R111121211 : good true 1 (pref true [1,1,1,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R111121212 : good true 1 (pref true [1,1,1,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R11112111 : good true 1 (pref true [1,1,1,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111121111
  · change good true 1 (step (pref true [1,1,1,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111121112
theorem R11112112 : good true 1 (pref true [1,1,1,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111121120
  · change good true 1 (step (pref true [1,1,1,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111121121
  · exact (hk (by decide)).elim
theorem R11112120 : good true 1 (pref true [1,1,1,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111121200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111121202
theorem R11112121 : good true 1 (pref true [1,1,1,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111121211
  · change good true 1 (step (pref true [1,1,1,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111121212
theorem R1111211 : good true 1 (pref true [1,1,1,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11112111
  · change good true 1 (step (pref true [1,1,1,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11112112
theorem R1111212 : good true 1 (pref true [1,1,1,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,1,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11112120
  · change good true 1 (step (pref true [1,1,1,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11112121
  · exact (hk (by decide)).elim
theorem R111121 : good true 1 (pref true [1,1,1,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,1,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1111211
  · change good true 1 (step (pref true [1,1,1,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1111212
end Ribbon5Owner
