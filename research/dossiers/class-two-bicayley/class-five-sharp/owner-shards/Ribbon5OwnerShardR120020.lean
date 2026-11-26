import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R120020000 : good true 2 (pref true [2,0,0,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R120020002 : good true 2 (pref true [2,0,0,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R120020020 : good true 2 (pref true [2,0,0,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R120020021 : good true 2 (pref true [2,0,0,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R120020200 : good true 2 (pref true [2,0,0,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R120020202 : good true 2 (pref true [2,0,0,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R120020211 : good true 2 (pref true [2,0,0,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R120020212 : good true 2 (pref true [2,0,0,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R12002000 : good true 2 (pref true [2,0,0,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120020000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120020002
theorem R12002002 : good true 2 (pref true [2,0,0,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120020020
  · change good true 2 (step (pref true [2,0,0,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120020021
  · exact (hk (by decide)).elim
theorem R12002020 : good true 2 (pref true [2,0,0,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120020200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120020202
theorem R12002021 : good true 2 (pref true [2,0,0,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120020211
  · change good true 2 (step (pref true [2,0,0,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120020212
theorem R1200200 : good true 2 (pref true [2,0,0,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12002000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12002002
theorem R1200202 : good true 2 (pref true [2,0,0,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12002020
  · change good true 2 (step (pref true [2,0,0,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12002021
  · exact (hk (by decide)).elim
theorem R120020 : good true 2 (pref true [2,0,0,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1200200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1200202
end Ribbon5Owner
