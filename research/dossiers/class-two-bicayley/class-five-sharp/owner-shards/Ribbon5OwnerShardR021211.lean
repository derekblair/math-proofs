import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R021211111 : good false 2 (pref false [2,1,2,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R021211112 : good false 2 (pref false [2,1,2,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R021211120 : good false 2 (pref false [2,1,2,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R021211121 : good false 2 (pref false [2,1,2,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R021211200 : good false 2 (pref false [2,1,2,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R021211202 : good false 2 (pref false [2,1,2,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R021211211 : good false 2 (pref false [2,1,2,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R021211212 : good false 2 (pref false [2,1,2,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R02121111 : good false 2 (pref false [2,1,2,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021211111
  · change good false 2 (step (pref false [2,1,2,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021211112
theorem R02121112 : good false 2 (pref false [2,1,2,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021211120
  · change good false 2 (step (pref false [2,1,2,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021211121
  · exact (hk (by decide)).elim
theorem R02121120 : good false 2 (pref false [2,1,2,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021211200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021211202
theorem R02121121 : good false 2 (pref false [2,1,2,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021211211
  · change good false 2 (step (pref false [2,1,2,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021211212
theorem R0212111 : good false 2 (pref false [2,1,2,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02121111
  · change good false 2 (step (pref false [2,1,2,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02121112
theorem R0212112 : good false 2 (pref false [2,1,2,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02121120
  · change good false 2 (step (pref false [2,1,2,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02121121
  · exact (hk (by decide)).elim
theorem R021211 : good false 2 (pref false [2,1,2,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0212111
  · change good false 2 (step (pref false [2,1,2,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0212112
end Ribbon5Owner
