import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R000020000 : good false 0 (pref false [0,0,0,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R000020002 : good false 0 (pref false [0,0,0,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R000020020 : good false 0 (pref false [0,0,0,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R000020021 : good false 0 (pref false [0,0,0,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R000020200 : good false 0 (pref false [0,0,0,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R000020202 : good false 0 (pref false [0,0,0,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R000020211 : good false 0 (pref false [0,0,0,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R000020212 : good false 0 (pref false [0,0,0,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R00002000 : good false 0 (pref false [0,0,0,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000020000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000020002
theorem R00002002 : good false 0 (pref false [0,0,0,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000020020
  · change good false 0 (step (pref false [0,0,0,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000020021
  · exact (hk (by decide)).elim
theorem R00002020 : good false 0 (pref false [0,0,0,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000020200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000020202
theorem R00002021 : good false 0 (pref false [0,0,0,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000020211
  · change good false 0 (step (pref false [0,0,0,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000020212
theorem R0000200 : good false 0 (pref false [0,0,0,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00002000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00002002
theorem R0000202 : good false 0 (pref false [0,0,0,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00002020
  · change good false 0 (step (pref false [0,0,0,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00002021
  · exact (hk (by decide)).elim
theorem R000020 : good false 0 (pref false [0,0,0,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0000200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0000202
end Ribbon5Owner
