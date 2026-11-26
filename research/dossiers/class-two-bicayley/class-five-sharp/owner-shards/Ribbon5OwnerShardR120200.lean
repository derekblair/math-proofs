import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R120200000 : good true 2 (pref true [2,0,2,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R120200002 : good true 2 (pref true [2,0,2,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R120200020 : good true 2 (pref true [2,0,2,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R120200021 : good true 2 (pref true [2,0,2,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R120200200 : good true 2 (pref true [2,0,2,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R120200202 : good true 2 (pref true [2,0,2,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R120200211 : good true 2 (pref true [2,0,2,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R120200212 : good true 2 (pref true [2,0,2,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R12020000 : good true 2 (pref true [2,0,2,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120200000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120200002
theorem R12020002 : good true 2 (pref true [2,0,2,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120200020
  · change good true 2 (step (pref true [2,0,2,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120200021
  · exact (hk (by decide)).elim
theorem R12020020 : good true 2 (pref true [2,0,2,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120200200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120200202
theorem R12020021 : good true 2 (pref true [2,0,2,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120200211
  · change good true 2 (step (pref true [2,0,2,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120200212
theorem R1202000 : good true 2 (pref true [2,0,2,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12020000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12020002
theorem R1202002 : good true 2 (pref true [2,0,2,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12020020
  · change good true 2 (step (pref true [2,0,2,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12020021
  · exact (hk (by decide)).elim
theorem R120200 : good true 2 (pref true [2,0,2,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1202000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1202002
end Ribbon5Owner
