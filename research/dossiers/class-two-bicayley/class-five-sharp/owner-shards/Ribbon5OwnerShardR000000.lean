import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R000000000 : good false 0 (pref false [0,0,0,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R000000002 : good false 0 (pref false [0,0,0,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R000000020 : good false 0 (pref false [0,0,0,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R000000021 : good false 0 (pref false [0,0,0,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R000000200 : good false 0 (pref false [0,0,0,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R000000202 : good false 0 (pref false [0,0,0,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R000000211 : good false 0 (pref false [0,0,0,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R000000212 : good false 0 (pref false [0,0,0,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R00000000 : good false 0 (pref false [0,0,0,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000000000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000000002
theorem R00000002 : good false 0 (pref false [0,0,0,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000000020
  · change good false 0 (step (pref false [0,0,0,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000000021
  · exact (hk (by decide)).elim
theorem R00000020 : good false 0 (pref false [0,0,0,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000000200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000000202
theorem R00000021 : good false 0 (pref false [0,0,0,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000000211
  · change good false 0 (step (pref false [0,0,0,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000000212
theorem R0000000 : good false 0 (pref false [0,0,0,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00000000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00000002
theorem R0000002 : good false 0 (pref false [0,0,0,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00000020
  · change good false 0 (step (pref false [0,0,0,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00000021
  · exact (hk (by decide)).elim
theorem R000000 : good false 0 (pref false [0,0,0,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0000000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0000002
end Ribbon5Owner
