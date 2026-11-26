import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R100211111 : good true 0 (pref true [0,0,2,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R100211112 : good true 0 (pref true [0,0,2,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R100211120 : good true 0 (pref true [0,0,2,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R100211121 : good true 0 (pref true [0,0,2,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R100211200 : good true 0 (pref true [0,0,2,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R100211202 : good true 0 (pref true [0,0,2,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R100211211 : good true 0 (pref true [0,0,2,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R100211212 : good true 0 (pref true [0,0,2,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R10021111 : good true 0 (pref true [0,0,2,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100211111
  · change good true 0 (step (pref true [0,0,2,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100211112
theorem R10021112 : good true 0 (pref true [0,0,2,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100211120
  · change good true 0 (step (pref true [0,0,2,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100211121
  · exact (hk (by decide)).elim
theorem R10021120 : good true 0 (pref true [0,0,2,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R100211200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100211202
theorem R10021121 : good true 0 (pref true [0,0,2,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R100211211
  · change good true 0 (step (pref true [0,0,2,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R100211212
theorem R1002111 : good true 0 (pref true [0,0,2,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10021111
  · change good true 0 (step (pref true [0,0,2,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10021112
theorem R1002112 : good true 0 (pref true [0,0,2,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,0,2,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10021120
  · change good true 0 (step (pref true [0,0,2,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10021121
  · exact (hk (by decide)).elim
theorem R100211 : good true 0 (pref true [0,0,2,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,0,2,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1002111
  · change good true 0 (step (pref true [0,0,2,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1002112
end Ribbon5Owner
