import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R011211111 : good false 1 (pref false [1,1,2,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R011211112 : good false 1 (pref false [1,1,2,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R011211120 : good false 1 (pref false [1,1,2,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R011211121 : good false 1 (pref false [1,1,2,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R011211200 : good false 1 (pref false [1,1,2,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R011211202 : good false 1 (pref false [1,1,2,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R011211211 : good false 1 (pref false [1,1,2,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R011211212 : good false 1 (pref false [1,1,2,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R01121111 : good false 1 (pref false [1,1,2,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011211111
  · change good false 1 (step (pref false [1,1,2,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011211112
theorem R01121112 : good false 1 (pref false [1,1,2,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011211120
  · change good false 1 (step (pref false [1,1,2,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011211121
  · exact (hk (by decide)).elim
theorem R01121120 : good false 1 (pref false [1,1,2,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011211200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011211202
theorem R01121121 : good false 1 (pref false [1,1,2,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011211211
  · change good false 1 (step (pref false [1,1,2,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011211212
theorem R0112111 : good false 1 (pref false [1,1,2,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01121111
  · change good false 1 (step (pref false [1,1,2,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01121112
theorem R0112112 : good false 1 (pref false [1,1,2,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01121120
  · change good false 1 (step (pref false [1,1,2,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01121121
  · exact (hk (by decide)).elim
theorem R011211 : good false 1 (pref false [1,1,2,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0112111
  · change good false 1 (step (pref false [1,1,2,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0112112
end Ribbon5Owner
