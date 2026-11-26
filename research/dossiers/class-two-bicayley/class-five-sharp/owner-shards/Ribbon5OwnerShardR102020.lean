import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R102020000 : good true 0 (pref true [0,2,0,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R102020002 : good true 0 (pref true [0,2,0,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R102020020 : good true 0 (pref true [0,2,0,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R102020021 : good true 0 (pref true [0,2,0,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R102020200 : good true 0 (pref true [0,2,0,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R102020202 : good true 0 (pref true [0,2,0,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R102020211 : good true 0 (pref true [0,2,0,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R102020212 : good true 0 (pref true [0,2,0,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R10202000 : good true 0 (pref true [0,2,0,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102020000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102020002
theorem R10202002 : good true 0 (pref true [0,2,0,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102020020
  · change good true 0 (step (pref true [0,2,0,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102020021
  · exact (hk (by decide)).elim
theorem R10202020 : good true 0 (pref true [0,2,0,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102020200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102020202
theorem R10202021 : good true 0 (pref true [0,2,0,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102020211
  · change good true 0 (step (pref true [0,2,0,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102020212
theorem R1020200 : good true 0 (pref true [0,2,0,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10202000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10202002
theorem R1020202 : good true 0 (pref true [0,2,0,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10202020
  · change good true 0 (step (pref true [0,2,0,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10202021
  · exact (hk (by decide)).elim
theorem R102020 : good true 0 (pref true [0,2,0,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1020200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1020202
end Ribbon5Owner
