import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R100021111 : good true 0 (pref true [0,0,0,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R100021112 : good true 0 (pref true [0,0,0,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R100021120 : good true 0 (pref true [0,0,0,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R100021121 : good true 0 (pref true [0,0,0,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R100021200 : good true 0 (pref true [0,0,0,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R100021202 : good true 0 (pref true [0,0,0,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R100021211 : good true 0 (pref true [0,0,0,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R100021212 : good true 0 (pref true [0,0,0,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R10002111 : good true 0 (pref true [0,0,0,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100021111
  · change good true 0 (step (pref true [0,0,0,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100021112
theorem R10002112 : good true 0 (pref true [0,0,0,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100021120
  · change good true 0 (step (pref true [0,0,0,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100021121
  · exact (hk (by decide)).elim
theorem R10002120 : good true 0 (pref true [0,0,0,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100021200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100021202
theorem R10002121 : good true 0 (pref true [0,0,0,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100021211
  · change good true 0 (step (pref true [0,0,0,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100021212
theorem R1000211 : good true 0 (pref true [0,0,0,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10002111
  · change good true 0 (step (pref true [0,0,0,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10002112
theorem R1000212 : good true 0 (pref true [0,0,0,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10002120
  · change good true 0 (step (pref true [0,0,0,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10002121
  · exact (hk (by decide)).elim
theorem R100021 : good true 0 (pref true [0,0,0,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1000211
  · change good true 0 (step (pref true [0,0,0,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1000212
end Ribbon5Owner
