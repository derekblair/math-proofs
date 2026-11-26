import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R120021111 : good true 2 (pref true [2,0,0,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R120021112 : good true 2 (pref true [2,0,0,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R120021120 : good true 2 (pref true [2,0,0,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R120021121 : good true 2 (pref true [2,0,0,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R120021200 : good true 2 (pref true [2,0,0,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R120021202 : good true 2 (pref true [2,0,0,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R120021211 : good true 2 (pref true [2,0,0,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R120021212 : good true 2 (pref true [2,0,0,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R12002111 : good true 2 (pref true [2,0,0,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120021111
  · change good true 2 (step (pref true [2,0,0,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120021112
theorem R12002112 : good true 2 (pref true [2,0,0,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120021120
  · change good true 2 (step (pref true [2,0,0,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120021121
  · exact (hk (by decide)).elim
theorem R12002120 : good true 2 (pref true [2,0,0,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R120021200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120021202
theorem R12002121 : good true 2 (pref true [2,0,0,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R120021211
  · change good true 2 (step (pref true [2,0,0,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R120021212
theorem R1200211 : good true 2 (pref true [2,0,0,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12002111
  · change good true 2 (step (pref true [2,0,0,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12002112
theorem R1200212 : good true 2 (pref true [2,0,0,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,0,0,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12002120
  · change good true 2 (step (pref true [2,0,0,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12002121
  · exact (hk (by decide)).elim
theorem R120021 : good true 2 (pref true [2,0,0,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,0,0,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1200211
  · change good true 2 (step (pref true [2,0,0,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1200212
end Ribbon5Owner
