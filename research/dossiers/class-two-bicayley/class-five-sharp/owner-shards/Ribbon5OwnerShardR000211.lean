import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R000211111 : good false 0 (pref false [0,0,2,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R000211112 : good false 0 (pref false [0,0,2,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R000211120 : good false 0 (pref false [0,0,2,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R000211121 : good false 0 (pref false [0,0,2,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R000211200 : good false 0 (pref false [0,0,2,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R000211202 : good false 0 (pref false [0,0,2,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R000211211 : good false 0 (pref false [0,0,2,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R000211212 : good false 0 (pref false [0,0,2,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R00021111 : good false 0 (pref false [0,0,2,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000211111
  · change good false 0 (step (pref false [0,0,2,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000211112
theorem R00021112 : good false 0 (pref false [0,0,2,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000211120
  · change good false 0 (step (pref false [0,0,2,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000211121
  · exact (hk (by decide)).elim
theorem R00021120 : good false 0 (pref false [0,0,2,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000211200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000211202
theorem R00021121 : good false 0 (pref false [0,0,2,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000211211
  · change good false 0 (step (pref false [0,0,2,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000211212
theorem R0002111 : good false 0 (pref false [0,0,2,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00021111
  · change good false 0 (step (pref false [0,0,2,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00021112
theorem R0002112 : good false 0 (pref false [0,0,2,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00021120
  · change good false 0 (step (pref false [0,0,2,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00021121
  · exact (hk (by decide)).elim
theorem R000211 : good false 0 (pref false [0,0,2,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0002111
  · change good false 0 (step (pref false [0,0,2,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0002112
end Ribbon5Owner
