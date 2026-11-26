import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R011120000 : good false 1 (pref false [1,1,1,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R011120002 : good false 1 (pref false [1,1,1,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R011120020 : good false 1 (pref false [1,1,1,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R011120021 : good false 1 (pref false [1,1,1,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R011120200 : good false 1 (pref false [1,1,1,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R011120202 : good false 1 (pref false [1,1,1,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R011120211 : good false 1 (pref false [1,1,1,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R011120212 : good false 1 (pref false [1,1,1,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R01112000 : good false 1 (pref false [1,1,1,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011120000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011120002
theorem R01112002 : good false 1 (pref false [1,1,1,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011120020
  · change good false 1 (step (pref false [1,1,1,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011120021
  · exact (hk (by decide)).elim
theorem R01112020 : good false 1 (pref false [1,1,1,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011120200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011120202
theorem R01112021 : good false 1 (pref false [1,1,1,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011120211
  · change good false 1 (step (pref false [1,1,1,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011120212
theorem R0111200 : good false 1 (pref false [1,1,1,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01112000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01112002
theorem R0111202 : good false 1 (pref false [1,1,1,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01112020
  · change good false 1 (step (pref false [1,1,1,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01112021
  · exact (hk (by decide)).elim
theorem R011120 : good false 1 (pref false [1,1,1,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0111200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0111202
end Ribbon5Owner
