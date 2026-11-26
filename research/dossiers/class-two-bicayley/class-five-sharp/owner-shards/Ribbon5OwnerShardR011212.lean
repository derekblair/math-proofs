import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R011212000 : good false 1 (pref false [1,1,2,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R011212002 : good false 1 (pref false [1,1,2,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R011212020 : good false 1 (pref false [1,1,2,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R011212021 : good false 1 (pref false [1,1,2,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R011212111 : good false 1 (pref false [1,1,2,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R011212112 : good false 1 (pref false [1,1,2,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R011212120 : good false 1 (pref false [1,1,2,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R011212121 : good false 1 (pref false [1,1,2,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R01121200 : good false 1 (pref false [1,1,2,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011212000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011212002
theorem R01121202 : good false 1 (pref false [1,1,2,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011212020
  · change good false 1 (step (pref false [1,1,2,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011212021
  · exact (hk (by decide)).elim
theorem R01121211 : good false 1 (pref false [1,1,2,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011212111
  · change good false 1 (step (pref false [1,1,2,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011212112
theorem R01121212 : good false 1 (pref false [1,1,2,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011212120
  · change good false 1 (step (pref false [1,1,2,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011212121
  · exact (hk (by decide)).elim
theorem R0112120 : good false 1 (pref false [1,1,2,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01121200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01121202
theorem R0112121 : good false 1 (pref false [1,1,2,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01121211
  · change good false 1 (step (pref false [1,1,2,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01121212
theorem R011212 : good false 1 (pref false [1,1,2,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0112120
  · change good false 1 (step (pref false [1,1,2,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0112121
  · exact (hk (by decide)).elim
end Ribbon5Owner
