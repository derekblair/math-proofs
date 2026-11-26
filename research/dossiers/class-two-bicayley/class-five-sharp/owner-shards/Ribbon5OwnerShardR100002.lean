import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R100002000 : good true 0 (pref true [0,0,0,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R100002002 : good true 0 (pref true [0,0,0,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R100002020 : good true 0 (pref true [0,0,0,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R100002021 : good true 0 (pref true [0,0,0,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R100002111 : good true 0 (pref true [0,0,0,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R100002112 : good true 0 (pref true [0,0,0,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R100002120 : good true 0 (pref true [0,0,0,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R100002121 : good true 0 (pref true [0,0,0,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R10000200 : good true 0 (pref true [0,0,0,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100002000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100002002
theorem R10000202 : good true 0 (pref true [0,0,0,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100002020
  · change good true 0 (step (pref true [0,0,0,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100002021
  · exact (hk (by decide)).elim
theorem R10000211 : good true 0 (pref true [0,0,0,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100002111
  · change good true 0 (step (pref true [0,0,0,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100002112
theorem R10000212 : good true 0 (pref true [0,0,0,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100002120
  · change good true 0 (step (pref true [0,0,0,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100002121
  · exact (hk (by decide)).elim
theorem R1000020 : good true 0 (pref true [0,0,0,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10000200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10000202
theorem R1000021 : good true 0 (pref true [0,0,0,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,0,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10000211
  · change good true 0 (step (pref true [0,0,0,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10000212
theorem R100002 : good true 0 (pref true [0,0,0,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,0,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1000020
  · change good true 0 (step (pref true [0,0,0,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1000021
  · exact (hk (by decide)).elim
end Ribbon5Owner
