import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R112111111 : good true 1 (pref true [1,2,1,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R112111112 : good true 1 (pref true [1,2,1,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R112111120 : good true 1 (pref true [1,2,1,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R112111121 : good true 1 (pref true [1,2,1,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R112111200 : good true 1 (pref true [1,2,1,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R112111202 : good true 1 (pref true [1,2,1,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R112111211 : good true 1 (pref true [1,2,1,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R112111212 : good true 1 (pref true [1,2,1,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R11211111 : good true 1 (pref true [1,2,1,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112111111
  · change good true 1 (step (pref true [1,2,1,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112111112
theorem R11211112 : good true 1 (pref true [1,2,1,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112111120
  · change good true 1 (step (pref true [1,2,1,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112111121
  · exact (hk (by decide)).elim
theorem R11211120 : good true 1 (pref true [1,2,1,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112111200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112111202
theorem R11211121 : good true 1 (pref true [1,2,1,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112111211
  · change good true 1 (step (pref true [1,2,1,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112111212
theorem R1121111 : good true 1 (pref true [1,2,1,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11211111
  · change good true 1 (step (pref true [1,2,1,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11211112
theorem R1121112 : good true 1 (pref true [1,2,1,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11211120
  · change good true 1 (step (pref true [1,2,1,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11211121
  · exact (hk (by decide)).elim
theorem R112111 : good true 1 (pref true [1,2,1,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1121111
  · change good true 1 (step (pref true [1,2,1,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1121112
end Ribbon5Owner
