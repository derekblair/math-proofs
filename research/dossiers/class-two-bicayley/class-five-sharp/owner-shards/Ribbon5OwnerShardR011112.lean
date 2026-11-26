import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R011112000 : good false 1 (pref false [1,1,1,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R011112002 : good false 1 (pref false [1,1,1,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R011112020 : good false 1 (pref false [1,1,1,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R011112021 : good false 1 (pref false [1,1,1,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R011112111 : good false 1 (pref false [1,1,1,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R011112112 : good false 1 (pref false [1,1,1,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R011112120 : good false 1 (pref false [1,1,1,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R011112121 : good false 1 (pref false [1,1,1,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R01111200 : good false 1 (pref false [1,1,1,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011112000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011112002
theorem R01111202 : good false 1 (pref false [1,1,1,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011112020
  · change good false 1 (step (pref false [1,1,1,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011112021
  · exact (hk (by decide)).elim
theorem R01111211 : good false 1 (pref false [1,1,1,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011112111
  · change good false 1 (step (pref false [1,1,1,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011112112
theorem R01111212 : good false 1 (pref false [1,1,1,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011112120
  · change good false 1 (step (pref false [1,1,1,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011112121
  · exact (hk (by decide)).elim
theorem R0111120 : good false 1 (pref false [1,1,1,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01111200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01111202
theorem R0111121 : good false 1 (pref false [1,1,1,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01111211
  · change good false 1 (step (pref false [1,1,1,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01111212
theorem R011112 : good false 1 (pref false [1,1,1,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0111120
  · change good false 1 (step (pref false [1,1,1,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0111121
  · exact (hk (by decide)).elim
end Ribbon5Owner
