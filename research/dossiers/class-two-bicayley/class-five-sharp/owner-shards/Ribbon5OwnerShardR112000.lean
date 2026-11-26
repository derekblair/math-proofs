import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R112000000 : good true 1 (pref true [1,2,0,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R112000002 : good true 1 (pref true [1,2,0,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R112000020 : good true 1 (pref true [1,2,0,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R112000021 : good true 1 (pref true [1,2,0,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R112000200 : good true 1 (pref true [1,2,0,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R112000202 : good true 1 (pref true [1,2,0,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R112000211 : good true 1 (pref true [1,2,0,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R112000212 : good true 1 (pref true [1,2,0,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R11200000 : good true 1 (pref true [1,2,0,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112000000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112000002
theorem R11200002 : good true 1 (pref true [1,2,0,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112000020
  · change good true 1 (step (pref true [1,2,0,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112000021
  · exact (hk (by decide)).elim
theorem R11200020 : good true 1 (pref true [1,2,0,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112000200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112000202
theorem R11200021 : good true 1 (pref true [1,2,0,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112000211
  · change good true 1 (step (pref true [1,2,0,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112000212
theorem R1120000 : good true 1 (pref true [1,2,0,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11200000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11200002
theorem R1120002 : good true 1 (pref true [1,2,0,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11200020
  · change good true 1 (step (pref true [1,2,0,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11200021
  · exact (hk (by decide)).elim
theorem R112000 : good true 1 (pref true [1,2,0,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1120000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1120002
end Ribbon5Owner
