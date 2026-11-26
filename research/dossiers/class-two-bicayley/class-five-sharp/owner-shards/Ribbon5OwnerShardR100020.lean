import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R100020000 : good true 0 (pref true [0,0,0,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R100020002 : good true 0 (pref true [0,0,0,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R100020020 : good true 0 (pref true [0,0,0,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R100020021 : good true 0 (pref true [0,0,0,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R100020200 : good true 0 (pref true [0,0,0,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R100020202 : good true 0 (pref true [0,0,0,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R100020211 : good true 0 (pref true [0,0,0,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R100020212 : good true 0 (pref true [0,0,0,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R10002000 : good true 0 (pref true [0,0,0,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100020000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100020002
theorem R10002002 : good true 0 (pref true [0,0,0,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100020020
  · change good true 0 (step (pref true [0,0,0,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100020021
  · exact (hk (by decide)).elim
theorem R10002020 : good true 0 (pref true [0,0,0,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100020200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100020202
theorem R10002021 : good true 0 (pref true [0,0,0,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100020211
  · change good true 0 (step (pref true [0,0,0,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100020212
theorem R1000200 : good true 0 (pref true [0,0,0,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10002000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10002002
theorem R1000202 : good true 0 (pref true [0,0,0,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10002020
  · change good true 0 (step (pref true [0,0,0,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10002021
  · exact (hk (by decide)).elim
theorem R100020 : good true 0 (pref true [0,0,0,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1000200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1000202
end Ribbon5Owner
