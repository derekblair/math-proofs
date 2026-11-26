import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R100212000 : good true 0 (pref true [0,0,2,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R100212002 : good true 0 (pref true [0,0,2,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R100212020 : good true 0 (pref true [0,0,2,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R100212021 : good true 0 (pref true [0,0,2,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R100212111 : good true 0 (pref true [0,0,2,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R100212112 : good true 0 (pref true [0,0,2,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R100212120 : good true 0 (pref true [0,0,2,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R100212121 : good true 0 (pref true [0,0,2,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R10021200 : good true 0 (pref true [0,0,2,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100212000
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100212002
theorem R10021202 : good true 0 (pref true [0,0,2,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100212020
  · change good true 0 (step (pref true [0,0,2,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100212021
  · exact (hk (by decide)).elim
theorem R10021211 : good true 0 (pref true [0,0,2,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100212111
  · change good true 0 (step (pref true [0,0,2,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100212112
theorem R10021212 : good true 0 (pref true [0,0,2,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100212120
  · change good true 0 (step (pref true [0,0,2,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100212121
  · exact (hk (by decide)).elim
theorem R1002120 : good true 0 (pref true [0,0,2,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10021200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10021202
theorem R1002121 : good true 0 (pref true [0,0,2,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10021211
  · change good true 0 (step (pref true [0,0,2,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10021212
theorem R100212 : good true 0 (pref true [0,0,2,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1002120
  · change good true 0 (step (pref true [0,0,2,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1002121
  · exact (hk (by decide)).elim
end Ribbon5Owner
