import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R102000000 : good true 0 (pref true [0,2,0,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R102000002 : good true 0 (pref true [0,2,0,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R102000020 : good true 0 (pref true [0,2,0,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R102000021 : good true 0 (pref true [0,2,0,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R102000200 : good true 0 (pref true [0,2,0,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R102000202 : good true 0 (pref true [0,2,0,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R102000211 : good true 0 (pref true [0,2,0,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R102000212 : good true 0 (pref true [0,2,0,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R10200000 : good true 0 (pref true [0,2,0,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102000000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102000002
theorem R10200002 : good true 0 (pref true [0,2,0,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102000020
  · change good true 0 (step (pref true [0,2,0,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102000021
  · exact (hk (by decide)).elim
theorem R10200020 : good true 0 (pref true [0,2,0,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102000200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102000202
theorem R10200021 : good true 0 (pref true [0,2,0,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102000211
  · change good true 0 (step (pref true [0,2,0,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102000212
theorem R1020000 : good true 0 (pref true [0,2,0,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10200000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10200002
theorem R1020002 : good true 0 (pref true [0,2,0,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10200020
  · change good true 0 (step (pref true [0,2,0,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10200021
  · exact (hk (by decide)).elim
theorem R102000 : good true 0 (pref true [0,2,0,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1020000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1020002
end Ribbon5Owner
