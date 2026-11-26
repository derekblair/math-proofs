import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R112002000 : good true 1 (pref true [1,2,0,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R112002002 : good true 1 (pref true [1,2,0,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R112002020 : good true 1 (pref true [1,2,0,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R112002021 : good true 1 (pref true [1,2,0,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R112002111 : good true 1 (pref true [1,2,0,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R112002112 : good true 1 (pref true [1,2,0,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R112002120 : good true 1 (pref true [1,2,0,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R112002121 : good true 1 (pref true [1,2,0,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R11200200 : good true 1 (pref true [1,2,0,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112002000
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112002002
theorem R11200202 : good true 1 (pref true [1,2,0,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112002020
  · change good true 1 (step (pref true [1,2,0,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112002021
  · exact (hk (by decide)).elim
theorem R11200211 : good true 1 (pref true [1,2,0,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112002111
  · change good true 1 (step (pref true [1,2,0,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R112002112
theorem R11200212 : good true 1 (pref true [1,2,0,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R112002120
  · change good true 1 (step (pref true [1,2,0,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R112002121
  · exact (hk (by decide)).elim
theorem R1120020 : good true 1 (pref true [1,2,0,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11200200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11200202
theorem R1120021 : good true 1 (pref true [1,2,0,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,2,0,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11200211
  · change good true 1 (step (pref true [1,2,0,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11200212
theorem R112002 : good true 1 (pref true [1,2,0,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,2,0,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1120020
  · change good true 1 (step (pref true [1,2,0,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1120021
  · exact (hk (by decide)).elim
end Ribbon5Owner
