import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R111211111 : good true 1 (pref true [1,1,2,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R111211112 : good true 1 (pref true [1,1,2,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R111211120 : good true 1 (pref true [1,1,2,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R111211121 : good true 1 (pref true [1,1,2,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R111211200 : good true 1 (pref true [1,1,2,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R111211202 : good true 1 (pref true [1,1,2,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R111211211 : good true 1 (pref true [1,1,2,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R111211212 : good true 1 (pref true [1,1,2,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R11121111 : good true 1 (pref true [1,1,2,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111211111
  · change good true 1 (step (pref true [1,1,2,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111211112
theorem R11121112 : good true 1 (pref true [1,1,2,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111211120
  · change good true 1 (step (pref true [1,1,2,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111211121
  · exact (hk (by decide)).elim
theorem R11121120 : good true 1 (pref true [1,1,2,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R111211200
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111211202
theorem R11121121 : good true 1 (pref true [1,1,2,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R111211211
  · change good true 1 (step (pref true [1,1,2,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R111211212
theorem R1112111 : good true 1 (pref true [1,1,2,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11121111
  · change good true 1 (step (pref true [1,1,2,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R11121112
theorem R1112112 : good true 1 (pref true [1,1,2,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 1 (step (pref true [1,1,2,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R11121120
  · change good true 1 (step (pref true [1,1,2,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R11121121
  · exact (hk (by decide)).elim
theorem R111211 : good true 1 (pref true [1,1,2,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 1 (step (pref true [1,1,2,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1112111
  · change good true 1 (step (pref true [1,1,2,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1112112
end Ribbon5Owner
