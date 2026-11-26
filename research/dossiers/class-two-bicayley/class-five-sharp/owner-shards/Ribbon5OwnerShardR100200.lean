import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R100200000 : good true 0 (pref true [0,0,2,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R100200002 : good true 0 (pref true [0,0,2,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R100200020 : good true 0 (pref true [0,0,2,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R100200021 : good true 0 (pref true [0,0,2,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R100200200 : good true 0 (pref true [0,0,2,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R100200202 : good true 0 (pref true [0,0,2,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R100200211 : good true 0 (pref true [0,0,2,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R100200212 : good true 0 (pref true [0,0,2,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R10020000 : good true 0 (pref true [0,0,2,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100200000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100200002
theorem R10020002 : good true 0 (pref true [0,0,2,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100200020
  · change good true 0 (step (pref true [0,0,2,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100200021
  · exact (hk (by decide)).elim
theorem R10020020 : good true 0 (pref true [0,0,2,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100200200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100200202
theorem R10020021 : good true 0 (pref true [0,0,2,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100200211
  · change good true 0 (step (pref true [0,0,2,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100200212
theorem R1002000 : good true 0 (pref true [0,0,2,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10020000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10020002
theorem R1002002 : good true 0 (pref true [0,0,2,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10020020
  · change good true 0 (step (pref true [0,0,2,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10020021
  · exact (hk (by decide)).elim
theorem R100200 : good true 0 (pref true [0,0,2,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1002000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1002002
end Ribbon5Owner
