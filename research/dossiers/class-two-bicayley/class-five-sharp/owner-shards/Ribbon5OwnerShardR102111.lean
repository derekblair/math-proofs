import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R102111111 : good true 0 (pref true [0,2,1,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R102111112 : good true 0 (pref true [0,2,1,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R102111120 : good true 0 (pref true [0,2,1,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R102111121 : good true 0 (pref true [0,2,1,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R102111200 : good true 0 (pref true [0,2,1,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R102111202 : good true 0 (pref true [0,2,1,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R102111211 : good true 0 (pref true [0,2,1,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R102111212 : good true 0 (pref true [0,2,1,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R10211111 : good true 0 (pref true [0,2,1,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102111111
  · change good true 0 (step (pref true [0,2,1,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102111112
theorem R10211112 : good true 0 (pref true [0,2,1,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102111120
  · change good true 0 (step (pref true [0,2,1,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102111121
  · exact (hk (by decide)).elim
theorem R10211120 : good true 0 (pref true [0,2,1,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R102111200
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102111202
theorem R10211121 : good true 0 (pref true [0,2,1,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R102111211
  · change good true 0 (step (pref true [0,2,1,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R102111212
theorem R1021111 : good true 0 (pref true [0,2,1,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10211111
  · change good true 0 (step (pref true [0,2,1,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R10211112
theorem R1021112 : good true 0 (pref true [0,2,1,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 0 (step (pref true [0,2,1,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R10211120
  · change good true 0 (step (pref true [0,2,1,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R10211121
  · exact (hk (by decide)).elim
theorem R102111 : good true 0 (pref true [0,2,1,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 0 (step (pref true [0,2,1,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1021111
  · change good true 0 (step (pref true [0,2,1,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1021112
end Ribbon5Owner
