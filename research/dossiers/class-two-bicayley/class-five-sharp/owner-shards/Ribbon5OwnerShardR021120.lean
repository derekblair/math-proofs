import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R021120000 : good false 2 (pref false [2,1,1,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R021120002 : good false 2 (pref false [2,1,1,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R021120020 : good false 2 (pref false [2,1,1,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R021120021 : good false 2 (pref false [2,1,1,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R021120200 : good false 2 (pref false [2,1,1,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R021120202 : good false 2 (pref false [2,1,1,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R021120211 : good false 2 (pref false [2,1,1,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R021120212 : good false 2 (pref false [2,1,1,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R02112000 : good false 2 (pref false [2,1,1,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021120000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021120002
theorem R02112002 : good false 2 (pref false [2,1,1,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021120020
  · change good false 2 (step (pref false [2,1,1,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021120021
  · exact (hk (by decide)).elim
theorem R02112020 : good false 2 (pref false [2,1,1,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021120200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021120202
theorem R02112021 : good false 2 (pref false [2,1,1,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021120211
  · change good false 2 (step (pref false [2,1,1,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021120212
theorem R0211200 : good false 2 (pref false [2,1,1,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02112000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02112002
theorem R0211202 : good false 2 (pref false [2,1,1,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02112020
  · change good false 2 (step (pref false [2,1,1,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02112021
  · exact (hk (by decide)).elim
theorem R021120 : good false 2 (pref false [2,1,1,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0211200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0211202
end Ribbon5Owner
