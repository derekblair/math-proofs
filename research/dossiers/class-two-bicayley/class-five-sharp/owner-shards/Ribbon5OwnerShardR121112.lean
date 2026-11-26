import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R121112000 : good true 2 (pref true [2,1,1,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R121112002 : good true 2 (pref true [2,1,1,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R121112020 : good true 2 (pref true [2,1,1,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R121112021 : good true 2 (pref true [2,1,1,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R121112111 : good true 2 (pref true [2,1,1,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R121112112 : good true 2 (pref true [2,1,1,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R121112120 : good true 2 (pref true [2,1,1,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R121112121 : good true 2 (pref true [2,1,1,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R12111200 : good true 2 (pref true [2,1,1,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121112000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121112002
theorem R12111202 : good true 2 (pref true [2,1,1,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121112020
  · change good true 2 (step (pref true [2,1,1,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121112021
  · exact (hk (by decide)).elim
theorem R12111211 : good true 2 (pref true [2,1,1,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121112111
  · change good true 2 (step (pref true [2,1,1,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121112112
theorem R12111212 : good true 2 (pref true [2,1,1,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121112120
  · change good true 2 (step (pref true [2,1,1,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121112121
  · exact (hk (by decide)).elim
theorem R1211120 : good true 2 (pref true [2,1,1,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12111200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12111202
theorem R1211121 : good true 2 (pref true [2,1,1,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12111211
  · change good true 2 (step (pref true [2,1,1,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12111212
theorem R121112 : good true 2 (pref true [2,1,1,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1211120
  · change good true 2 (step (pref true [2,1,1,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1211121
  · exact (hk (by decide)).elim
end Ribbon5Owner
