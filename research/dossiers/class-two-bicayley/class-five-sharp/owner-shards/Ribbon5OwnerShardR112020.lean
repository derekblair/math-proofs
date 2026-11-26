import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R112020000 : good true 1 (pref true [1,2,0,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R112020002 : good true 1 (pref true [1,2,0,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R112020020 : good true 1 (pref true [1,2,0,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R112020021 : good true 1 (pref true [1,2,0,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R112020200 : good true 1 (pref true [1,2,0,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R112020202 : good true 1 (pref true [1,2,0,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R112020211 : good true 1 (pref true [1,2,0,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R112020212 : good true 1 (pref true [1,2,0,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R11202000 : good true 1 (pref true [1,2,0,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112020000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112020002
theorem R11202002 : good true 1 (pref true [1,2,0,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112020020
  · change good true 1 (step (pref true [1,2,0,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112020021
  · exact (hk (by decide)).elim
theorem R11202020 : good true 1 (pref true [1,2,0,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112020200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112020202
theorem R11202021 : good true 1 (pref true [1,2,0,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112020211
  · change good true 1 (step (pref true [1,2,0,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112020212
theorem R1120200 : good true 1 (pref true [1,2,0,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11202000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11202002
theorem R1120202 : good true 1 (pref true [1,2,0,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11202020
  · change good true 1 (step (pref true [1,2,0,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11202021
  · exact (hk (by decide)).elim
theorem R112020 : good true 1 (pref true [1,2,0,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1120200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1120202
end Ribbon5Owner
