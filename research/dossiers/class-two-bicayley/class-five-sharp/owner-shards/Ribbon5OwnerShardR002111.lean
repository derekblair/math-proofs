import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R002111111 : good false 0 (pref false [0,2,1,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R002111112 : good false 0 (pref false [0,2,1,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R002111120 : good false 0 (pref false [0,2,1,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R002111121 : good false 0 (pref false [0,2,1,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R002111200 : good false 0 (pref false [0,2,1,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R002111202 : good false 0 (pref false [0,2,1,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R002111211 : good false 0 (pref false [0,2,1,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R002111212 : good false 0 (pref false [0,2,1,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R00211111 : good false 0 (pref false [0,2,1,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002111111
  · change good false 0 (step (pref false [0,2,1,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002111112
theorem R00211112 : good false 0 (pref false [0,2,1,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002111120
  · change good false 0 (step (pref false [0,2,1,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002111121
  · exact (hk (by decide)).elim
theorem R00211120 : good false 0 (pref false [0,2,1,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002111200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002111202
theorem R00211121 : good false 0 (pref false [0,2,1,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002111211
  · change good false 0 (step (pref false [0,2,1,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002111212
theorem R0021111 : good false 0 (pref false [0,2,1,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00211111
  · change good false 0 (step (pref false [0,2,1,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00211112
theorem R0021112 : good false 0 (pref false [0,2,1,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00211120
  · change good false 0 (step (pref false [0,2,1,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00211121
  · exact (hk (by decide)).elim
theorem R002111 : good false 0 (pref false [0,2,1,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0021111
  · change good false 0 (step (pref false [0,2,1,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0021112
end Ribbon5Owner
