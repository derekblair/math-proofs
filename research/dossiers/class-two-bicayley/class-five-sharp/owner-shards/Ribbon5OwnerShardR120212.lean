import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R120212000 : good true 2 (pref true [2,0,2,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R120212002 : good true 2 (pref true [2,0,2,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R120212020 : good true 2 (pref true [2,0,2,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R120212021 : good true 2 (pref true [2,0,2,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R120212111 : good true 2 (pref true [2,0,2,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R120212112 : good true 2 (pref true [2,0,2,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R120212120 : good true 2 (pref true [2,0,2,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R120212121 : good true 2 (pref true [2,0,2,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R12021200 : good true 2 (pref true [2,0,2,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120212000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120212002
theorem R12021202 : good true 2 (pref true [2,0,2,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120212020
  · change good true 2 (step (pref true [2,0,2,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120212021
  · exact (hk (by decide)).elim
theorem R12021211 : good true 2 (pref true [2,0,2,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120212111
  · change good true 2 (step (pref true [2,0,2,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120212112
theorem R12021212 : good true 2 (pref true [2,0,2,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120212120
  · change good true 2 (step (pref true [2,0,2,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120212121
  · exact (hk (by decide)).elim
theorem R1202120 : good true 2 (pref true [2,0,2,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12021200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12021202
theorem R1202121 : good true 2 (pref true [2,0,2,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12021211
  · change good true 2 (step (pref true [2,0,2,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12021212
theorem R120212 : good true 2 (pref true [2,0,2,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1202120
  · change good true 2 (step (pref true [2,0,2,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1202121
  · exact (hk (by decide)).elim
end Ribbon5Owner
