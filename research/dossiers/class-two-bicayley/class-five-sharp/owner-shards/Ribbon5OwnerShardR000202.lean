import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R000202000 : good false 0 (pref false [0,0,2,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R000202002 : good false 0 (pref false [0,0,2,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R000202020 : good false 0 (pref false [0,0,2,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R000202021 : good false 0 (pref false [0,0,2,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R000202111 : good false 0 (pref false [0,0,2,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R000202112 : good false 0 (pref false [0,0,2,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R000202120 : good false 0 (pref false [0,0,2,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R000202121 : good false 0 (pref false [0,0,2,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R00020200 : good false 0 (pref false [0,0,2,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000202000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000202002
theorem R00020202 : good false 0 (pref false [0,0,2,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000202020
  · change good false 0 (step (pref false [0,0,2,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000202021
  · exact (hk (by decide)).elim
theorem R00020211 : good false 0 (pref false [0,0,2,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000202111
  · change good false 0 (step (pref false [0,0,2,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000202112
theorem R00020212 : good false 0 (pref false [0,0,2,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000202120
  · change good false 0 (step (pref false [0,0,2,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000202121
  · exact (hk (by decide)).elim
theorem R0002020 : good false 0 (pref false [0,0,2,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00020200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00020202
theorem R0002021 : good false 0 (pref false [0,0,2,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00020211
  · change good false 0 (step (pref false [0,0,2,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00020212
theorem R000202 : good false 0 (pref false [0,0,2,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0002020
  · change good false 0 (step (pref false [0,0,2,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0002021
  · exact (hk (by decide)).elim
end Ribbon5Owner
