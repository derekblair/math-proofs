import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R120002000 : good true 2 (pref true [2,0,0,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R120002002 : good true 2 (pref true [2,0,0,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R120002020 : good true 2 (pref true [2,0,0,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R120002021 : good true 2 (pref true [2,0,0,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R120002111 : good true 2 (pref true [2,0,0,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R120002112 : good true 2 (pref true [2,0,0,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R120002120 : good true 2 (pref true [2,0,0,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R120002121 : good true 2 (pref true [2,0,0,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R12000200 : good true 2 (pref true [2,0,0,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120002000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120002002
theorem R12000202 : good true 2 (pref true [2,0,0,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120002020
  · change good true 2 (step (pref true [2,0,0,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120002021
  · exact (hk (by decide)).elim
theorem R12000211 : good true 2 (pref true [2,0,0,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120002111
  · change good true 2 (step (pref true [2,0,0,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120002112
theorem R12000212 : good true 2 (pref true [2,0,0,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120002120
  · change good true 2 (step (pref true [2,0,0,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120002121
  · exact (hk (by decide)).elim
theorem R1200020 : good true 2 (pref true [2,0,0,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12000200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12000202
theorem R1200021 : good true 2 (pref true [2,0,0,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12000211
  · change good true 2 (step (pref true [2,0,0,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12000212
theorem R120002 : good true 2 (pref true [2,0,0,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1200020
  · change good true 2 (step (pref true [2,0,0,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1200021
  · exact (hk (by decide)).elim
end Ribbon5Owner
