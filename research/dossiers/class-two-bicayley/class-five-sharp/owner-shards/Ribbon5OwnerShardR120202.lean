import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R120202000 : good true 2 (pref true [2,0,2,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R120202002 : good true 2 (pref true [2,0,2,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R120202020 : good true 2 (pref true [2,0,2,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R120202021 : good true 2 (pref true [2,0,2,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R120202111 : good true 2 (pref true [2,0,2,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R120202112 : good true 2 (pref true [2,0,2,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R120202120 : good true 2 (pref true [2,0,2,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R120202121 : good true 2 (pref true [2,0,2,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R12020200 : good true 2 (pref true [2,0,2,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120202000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120202002
theorem R12020202 : good true 2 (pref true [2,0,2,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120202020
  · change good true 2 (step (pref true [2,0,2,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120202021
  · exact (hk (by decide)).elim
theorem R12020211 : good true 2 (pref true [2,0,2,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120202111
  · change good true 2 (step (pref true [2,0,2,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120202112
theorem R12020212 : good true 2 (pref true [2,0,2,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120202120
  · change good true 2 (step (pref true [2,0,2,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120202121
  · exact (hk (by decide)).elim
theorem R1202020 : good true 2 (pref true [2,0,2,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12020200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12020202
theorem R1202021 : good true 2 (pref true [2,0,2,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,2,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12020211
  · change good true 2 (step (pref true [2,0,2,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12020212
theorem R120202 : good true 2 (pref true [2,0,2,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,2,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1202020
  · change good true 2 (step (pref true [2,0,2,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1202021
  · exact (hk (by decide)).elim
end Ribbon5Owner
