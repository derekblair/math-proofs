import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R011111111 : good false 1 (pref false [1,1,1,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R011111112 : good false 1 (pref false [1,1,1,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R011111120 : good false 1 (pref false [1,1,1,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R011111121 : good false 1 (pref false [1,1,1,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R011111200 : good false 1 (pref false [1,1,1,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R011111202 : good false 1 (pref false [1,1,1,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R011111211 : good false 1 (pref false [1,1,1,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R011111212 : good false 1 (pref false [1,1,1,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R01111111 : good false 1 (pref false [1,1,1,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011111111
  · change good false 1 (step (pref false [1,1,1,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011111112
theorem R01111112 : good false 1 (pref false [1,1,1,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011111120
  · change good false 1 (step (pref false [1,1,1,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011111121
  · exact (hk (by decide)).elim
theorem R01111120 : good false 1 (pref false [1,1,1,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011111200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011111202
theorem R01111121 : good false 1 (pref false [1,1,1,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011111211
  · change good false 1 (step (pref false [1,1,1,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011111212
theorem R0111111 : good false 1 (pref false [1,1,1,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01111111
  · change good false 1 (step (pref false [1,1,1,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01111112
theorem R0111112 : good false 1 (pref false [1,1,1,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01111120
  · change good false 1 (step (pref false [1,1,1,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01111121
  · exact (hk (by decide)).elim
theorem R011111 : good false 1 (pref false [1,1,1,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0111111
  · change good false 1 (step (pref false [1,1,1,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0111112
end Ribbon5Owner
