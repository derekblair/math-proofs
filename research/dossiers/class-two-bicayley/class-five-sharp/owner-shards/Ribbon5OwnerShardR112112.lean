import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R112112000 : good true 1 (pref true [1,2,1,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R112112002 : good true 1 (pref true [1,2,1,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R112112020 : good true 1 (pref true [1,2,1,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R112112021 : good true 1 (pref true [1,2,1,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R112112111 : good true 1 (pref true [1,2,1,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R112112112 : good true 1 (pref true [1,2,1,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R112112120 : good true 1 (pref true [1,2,1,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R112112121 : good true 1 (pref true [1,2,1,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R11211200 : good true 1 (pref true [1,2,1,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112112000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112112002
theorem R11211202 : good true 1 (pref true [1,2,1,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112112020
  · change good true 1 (step (pref true [1,2,1,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112112021
  · exact (hk (by decide)).elim
theorem R11211211 : good true 1 (pref true [1,2,1,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112112111
  · change good true 1 (step (pref true [1,2,1,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112112112
theorem R11211212 : good true 1 (pref true [1,2,1,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112112120
  · change good true 1 (step (pref true [1,2,1,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112112121
  · exact (hk (by decide)).elim
theorem R1121120 : good true 1 (pref true [1,2,1,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11211200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11211202
theorem R1121121 : good true 1 (pref true [1,2,1,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,1,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11211211
  · change good true 1 (step (pref true [1,2,1,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11211212
theorem R112112 : good true 1 (pref true [1,2,1,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,1,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1121120
  · change good true 1 (step (pref true [1,2,1,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1121121
  · exact (hk (by decide)).elim
end Ribbon5Owner
