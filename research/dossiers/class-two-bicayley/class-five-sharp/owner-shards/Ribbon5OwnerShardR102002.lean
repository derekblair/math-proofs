import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R102002000 : good true 0 (pref true [0,2,0,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R102002002 : good true 0 (pref true [0,2,0,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R102002020 : good true 0 (pref true [0,2,0,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R102002021 : good true 0 (pref true [0,2,0,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R102002111 : good true 0 (pref true [0,2,0,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R102002112 : good true 0 (pref true [0,2,0,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R102002120 : good true 0 (pref true [0,2,0,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R102002121 : good true 0 (pref true [0,2,0,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R10200200 : good true 0 (pref true [0,2,0,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102002000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102002002
theorem R10200202 : good true 0 (pref true [0,2,0,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102002020
  · change good true 0 (step (pref true [0,2,0,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102002021
  · exact (hk (by decide)).elim
theorem R10200211 : good true 0 (pref true [0,2,0,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102002111
  · change good true 0 (step (pref true [0,2,0,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102002112
theorem R10200212 : good true 0 (pref true [0,2,0,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102002120
  · change good true 0 (step (pref true [0,2,0,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102002121
  · exact (hk (by decide)).elim
theorem R1020020 : good true 0 (pref true [0,2,0,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10200200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10200202
theorem R1020021 : good true 0 (pref true [0,2,0,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,0,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10200211
  · change good true 0 (step (pref true [0,2,0,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10200212
theorem R102002 : good true 0 (pref true [0,2,0,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,0,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1020020
  · change good true 0 (step (pref true [0,2,0,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1020021
  · exact (hk (by decide)).elim
end Ribbon5Owner
