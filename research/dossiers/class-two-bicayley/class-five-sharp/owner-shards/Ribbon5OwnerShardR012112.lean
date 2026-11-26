import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R012112000 : good false 1 (pref false [1,2,1,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R012112002 : good false 1 (pref false [1,2,1,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R012112020 : good false 1 (pref false [1,2,1,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R012112021 : good false 1 (pref false [1,2,1,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R012112111 : good false 1 (pref false [1,2,1,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R012112112 : good false 1 (pref false [1,2,1,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R012112120 : good false 1 (pref false [1,2,1,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R012112121 : good false 1 (pref false [1,2,1,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R01211200 : good false 1 (pref false [1,2,1,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012112000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012112002
theorem R01211202 : good false 1 (pref false [1,2,1,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012112020
  · change good false 1 (step (pref false [1,2,1,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012112021
  · exact (hk (by decide)).elim
theorem R01211211 : good false 1 (pref false [1,2,1,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012112111
  · change good false 1 (step (pref false [1,2,1,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012112112
theorem R01211212 : good false 1 (pref false [1,2,1,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012112120
  · change good false 1 (step (pref false [1,2,1,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012112121
  · exact (hk (by decide)).elim
theorem R0121120 : good false 1 (pref false [1,2,1,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01211200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01211202
theorem R0121121 : good false 1 (pref false [1,2,1,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01211211
  · change good false 1 (step (pref false [1,2,1,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01211212
theorem R012112 : good false 1 (pref false [1,2,1,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0121120
  · change good false 1 (step (pref false [1,2,1,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0121121
  · exact (hk (by decide)).elim
end Ribbon5Owner
