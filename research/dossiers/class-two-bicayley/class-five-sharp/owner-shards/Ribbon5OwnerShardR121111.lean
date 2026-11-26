import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R121111111 : good true 2 (pref true [2,1,1,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R121111112 : good true 2 (pref true [2,1,1,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R121111120 : good true 2 (pref true [2,1,1,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R121111121 : good true 2 (pref true [2,1,1,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R121111200 : good true 2 (pref true [2,1,1,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R121111202 : good true 2 (pref true [2,1,1,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R121111211 : good true 2 (pref true [2,1,1,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R121111212 : good true 2 (pref true [2,1,1,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R12111111 : good true 2 (pref true [2,1,1,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121111111
  · change good true 2 (step (pref true [2,1,1,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121111112
theorem R12111112 : good true 2 (pref true [2,1,1,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121111120
  · change good true 2 (step (pref true [2,1,1,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121111121
  · exact (hk (by decide)).elim
theorem R12111120 : good true 2 (pref true [2,1,1,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121111200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121111202
theorem R12111121 : good true 2 (pref true [2,1,1,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121111211
  · change good true 2 (step (pref true [2,1,1,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121111212
theorem R1211111 : good true 2 (pref true [2,1,1,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12111111
  · change good true 2 (step (pref true [2,1,1,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12111112
theorem R1211112 : good true 2 (pref true [2,1,1,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12111120
  · change good true 2 (step (pref true [2,1,1,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12111121
  · exact (hk (by decide)).elim
theorem R121111 : good true 2 (pref true [2,1,1,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1211111
  · change good true 2 (step (pref true [2,1,1,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1211112
end Ribbon5Owner
