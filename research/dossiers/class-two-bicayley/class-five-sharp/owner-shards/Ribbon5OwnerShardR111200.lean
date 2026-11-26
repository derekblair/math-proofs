import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R111200000 : good true 1 (pref true [1,1,2,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R111200002 : good true 1 (pref true [1,1,2,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R111200020 : good true 1 (pref true [1,1,2,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R111200021 : good true 1 (pref true [1,1,2,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R111200200 : good true 1 (pref true [1,1,2,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R111200202 : good true 1 (pref true [1,1,2,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R111200211 : good true 1 (pref true [1,1,2,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R111200212 : good true 1 (pref true [1,1,2,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R11120000 : good true 1 (pref true [1,1,2,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111200000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111200002
theorem R11120002 : good true 1 (pref true [1,1,2,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111200020
  · change good true 1 (step (pref true [1,1,2,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111200021
  · exact (hk (by decide)).elim
theorem R11120020 : good true 1 (pref true [1,1,2,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111200200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111200202
theorem R11120021 : good true 1 (pref true [1,1,2,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111200211
  · change good true 1 (step (pref true [1,1,2,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111200212
theorem R1112000 : good true 1 (pref true [1,1,2,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11120000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11120002
theorem R1112002 : good true 1 (pref true [1,1,2,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11120020
  · change good true 1 (step (pref true [1,1,2,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11120021
  · exact (hk (by decide)).elim
theorem R111200 : good true 1 (pref true [1,1,2,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1112000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1112002
end Ribbon5Owner
