import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R000212000 : good false 0 (pref false [0,0,2,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R000212002 : good false 0 (pref false [0,0,2,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R000212020 : good false 0 (pref false [0,0,2,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R000212021 : good false 0 (pref false [0,0,2,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R000212111 : good false 0 (pref false [0,0,2,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R000212112 : good false 0 (pref false [0,0,2,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R000212120 : good false 0 (pref false [0,0,2,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R000212121 : good false 0 (pref false [0,0,2,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R00021200 : good false 0 (pref false [0,0,2,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000212000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000212002
theorem R00021202 : good false 0 (pref false [0,0,2,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000212020
  · change good false 0 (step (pref false [0,0,2,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000212021
  · exact (hk (by decide)).elim
theorem R00021211 : good false 0 (pref false [0,0,2,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000212111
  · change good false 0 (step (pref false [0,0,2,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000212112
theorem R00021212 : good false 0 (pref false [0,0,2,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000212120
  · change good false 0 (step (pref false [0,0,2,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000212121
  · exact (hk (by decide)).elim
theorem R0002120 : good false 0 (pref false [0,0,2,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00021200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00021202
theorem R0002121 : good false 0 (pref false [0,0,2,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00021211
  · change good false 0 (step (pref false [0,0,2,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00021212
theorem R000212 : good false 0 (pref false [0,0,2,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0002120
  · change good false 0 (step (pref false [0,0,2,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0002121
  · exact (hk (by decide)).elim
end Ribbon5Owner
