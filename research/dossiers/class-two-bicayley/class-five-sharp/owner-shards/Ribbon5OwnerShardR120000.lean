import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R120000000 : good true 2 (pref true [2,0,0,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R120000002 : good true 2 (pref true [2,0,0,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R120000020 : good true 2 (pref true [2,0,0,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R120000021 : good true 2 (pref true [2,0,0,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R120000200 : good true 2 (pref true [2,0,0,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R120000202 : good true 2 (pref true [2,0,0,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R120000211 : good true 2 (pref true [2,0,0,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R120000212 : good true 2 (pref true [2,0,0,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R12000000 : good true 2 (pref true [2,0,0,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120000000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120000002
theorem R12000002 : good true 2 (pref true [2,0,0,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120000020
  · change good true 2 (step (pref true [2,0,0,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120000021
  · exact (hk (by decide)).elim
theorem R12000020 : good true 2 (pref true [2,0,0,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120000200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120000202
theorem R12000021 : good true 2 (pref true [2,0,0,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120000211
  · change good true 2 (step (pref true [2,0,0,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120000212
theorem R1200000 : good true 2 (pref true [2,0,0,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12000000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12000002
theorem R1200002 : good true 2 (pref true [2,0,0,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12000020
  · change good true 2 (step (pref true [2,0,0,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12000021
  · exact (hk (by decide)).elim
theorem R120000 : good true 2 (pref true [2,0,0,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1200000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1200002
end Ribbon5Owner
