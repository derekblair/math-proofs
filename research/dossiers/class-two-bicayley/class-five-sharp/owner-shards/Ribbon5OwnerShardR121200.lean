import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R121200000 : good true 2 (pref true [2,1,2,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R121200002 : good true 2 (pref true [2,1,2,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R121200020 : good true 2 (pref true [2,1,2,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R121200021 : good true 2 (pref true [2,1,2,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R121200200 : good true 2 (pref true [2,1,2,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R121200202 : good true 2 (pref true [2,1,2,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R121200211 : good true 2 (pref true [2,1,2,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R121200212 : good true 2 (pref true [2,1,2,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R12120000 : good true 2 (pref true [2,1,2,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121200000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121200002
theorem R12120002 : good true 2 (pref true [2,1,2,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121200020
  · change good true 2 (step (pref true [2,1,2,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121200021
  · exact (hk (by decide)).elim
theorem R12120020 : good true 2 (pref true [2,1,2,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121200200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121200202
theorem R12120021 : good true 2 (pref true [2,1,2,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121200211
  · change good true 2 (step (pref true [2,1,2,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121200212
theorem R1212000 : good true 2 (pref true [2,1,2,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12120000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12120002
theorem R1212002 : good true 2 (pref true [2,1,2,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12120020
  · change good true 2 (step (pref true [2,1,2,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12120021
  · exact (hk (by decide)).elim
theorem R121200 : good true 2 (pref true [2,1,2,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,2,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1212000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,2,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1212002
end Ribbon5Owner
