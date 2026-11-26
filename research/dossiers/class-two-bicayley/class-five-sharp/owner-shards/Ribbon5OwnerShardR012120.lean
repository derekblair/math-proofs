import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R012120000 : good false 1 (pref false [1,2,1,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R012120002 : good false 1 (pref false [1,2,1,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R012120020 : good false 1 (pref false [1,2,1,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R012120021 : good false 1 (pref false [1,2,1,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R012120200 : good false 1 (pref false [1,2,1,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R012120202 : good false 1 (pref false [1,2,1,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R012120211 : good false 1 (pref false [1,2,1,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R012120212 : good false 1 (pref false [1,2,1,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R01212000 : good false 1 (pref false [1,2,1,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012120000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012120002
theorem R01212002 : good false 1 (pref false [1,2,1,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012120020
  · change good false 1 (step (pref false [1,2,1,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012120021
  · exact (hk (by decide)).elim
theorem R01212020 : good false 1 (pref false [1,2,1,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012120200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012120202
theorem R01212021 : good false 1 (pref false [1,2,1,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012120211
  · change good false 1 (step (pref false [1,2,1,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012120212
theorem R0121200 : good false 1 (pref false [1,2,1,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01212000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01212002
theorem R0121202 : good false 1 (pref false [1,2,1,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01212020
  · change good false 1 (step (pref false [1,2,1,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01212021
  · exact (hk (by decide)).elim
theorem R012120 : good false 1 (pref false [1,2,1,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0121200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0121202
end Ribbon5Owner
