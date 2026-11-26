import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R020212000 : good false 2 (pref false [2,0,2,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R020212002 : good false 2 (pref false [2,0,2,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R020212020 : good false 2 (pref false [2,0,2,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R020212021 : good false 2 (pref false [2,0,2,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R020212111 : good false 2 (pref false [2,0,2,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R020212112 : good false 2 (pref false [2,0,2,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R020212120 : good false 2 (pref false [2,0,2,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R020212121 : good false 2 (pref false [2,0,2,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R02021200 : good false 2 (pref false [2,0,2,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020212000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020212002
theorem R02021202 : good false 2 (pref false [2,0,2,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020212020
  · change good false 2 (step (pref false [2,0,2,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020212021
  · exact (hk (by decide)).elim
theorem R02021211 : good false 2 (pref false [2,0,2,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020212111
  · change good false 2 (step (pref false [2,0,2,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020212112
theorem R02021212 : good false 2 (pref false [2,0,2,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020212120
  · change good false 2 (step (pref false [2,0,2,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020212121
  · exact (hk (by decide)).elim
theorem R0202120 : good false 2 (pref false [2,0,2,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02021200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02021202
theorem R0202121 : good false 2 (pref false [2,0,2,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02021211
  · change good false 2 (step (pref false [2,0,2,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02021212
theorem R020212 : good false 2 (pref false [2,0,2,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0202120
  · change good false 2 (step (pref false [2,0,2,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0202121
  · exact (hk (by decide)).elim
end Ribbon5Owner
