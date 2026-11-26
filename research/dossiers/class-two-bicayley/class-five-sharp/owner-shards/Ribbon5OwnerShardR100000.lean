import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R100000000 : good true 0 (pref true [0,0,0,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R100000002 : good true 0 (pref true [0,0,0,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R100000020 : good true 0 (pref true [0,0,0,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R100000021 : good true 0 (pref true [0,0,0,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R100000200 : good true 0 (pref true [0,0,0,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R100000202 : good true 0 (pref true [0,0,0,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R100000211 : good true 0 (pref true [0,0,0,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R100000212 : good true 0 (pref true [0,0,0,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R10000000 : good true 0 (pref true [0,0,0,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100000000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100000002
theorem R10000002 : good true 0 (pref true [0,0,0,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100000020
  · change good true 0 (step (pref true [0,0,0,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100000021
  · exact (hk (by decide)).elim
theorem R10000020 : good true 0 (pref true [0,0,0,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100000200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100000202
theorem R10000021 : good true 0 (pref true [0,0,0,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100000211
  · change good true 0 (step (pref true [0,0,0,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100000212
theorem R1000000 : good true 0 (pref true [0,0,0,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10000000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10000002
theorem R1000002 : good true 0 (pref true [0,0,0,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10000020
  · change good true 0 (step (pref true [0,0,0,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10000021
  · exact (hk (by decide)).elim
theorem R100000 : good true 0 (pref true [0,0,0,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1000000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1000002
end Ribbon5Owner
