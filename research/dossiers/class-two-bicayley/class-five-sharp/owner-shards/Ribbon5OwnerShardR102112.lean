import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R102112000 : good true 0 (pref true [0,2,1,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R102112002 : good true 0 (pref true [0,2,1,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R102112020 : good true 0 (pref true [0,2,1,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R102112021 : good true 0 (pref true [0,2,1,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R102112111 : good true 0 (pref true [0,2,1,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R102112112 : good true 0 (pref true [0,2,1,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R102112120 : good true 0 (pref true [0,2,1,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R102112121 : good true 0 (pref true [0,2,1,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R10211200 : good true 0 (pref true [0,2,1,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102112000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102112002
theorem R10211202 : good true 0 (pref true [0,2,1,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102112020
  · change good true 0 (step (pref true [0,2,1,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102112021
  · exact (hk (by decide)).elim
theorem R10211211 : good true 0 (pref true [0,2,1,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102112111
  · change good true 0 (step (pref true [0,2,1,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102112112
theorem R10211212 : good true 0 (pref true [0,2,1,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102112120
  · change good true 0 (step (pref true [0,2,1,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102112121
  · exact (hk (by decide)).elim
theorem R1021120 : good true 0 (pref true [0,2,1,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10211200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10211202
theorem R1021121 : good true 0 (pref true [0,2,1,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10211211
  · change good true 0 (step (pref true [0,2,1,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10211212
theorem R102112 : good true 0 (pref true [0,2,1,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1021120
  · change good true 0 (step (pref true [0,2,1,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1021121
  · exact (hk (by decide)).elim
end Ribbon5Owner
