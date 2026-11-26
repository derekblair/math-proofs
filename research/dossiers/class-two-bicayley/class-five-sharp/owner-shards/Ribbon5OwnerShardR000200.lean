import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R000200000 : good false 0 (pref false [0,0,2,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R000200002 : good false 0 (pref false [0,0,2,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R000200020 : good false 0 (pref false [0,0,2,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R000200021 : good false 0 (pref false [0,0,2,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R000200200 : good false 0 (pref false [0,0,2,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R000200202 : good false 0 (pref false [0,0,2,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R000200211 : good false 0 (pref false [0,0,2,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R000200212 : good false 0 (pref false [0,0,2,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R00020000 : good false 0 (pref false [0,0,2,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000200000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000200002
theorem R00020002 : good false 0 (pref false [0,0,2,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000200020
  · change good false 0 (step (pref false [0,0,2,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000200021
  · exact (hk (by decide)).elim
theorem R00020020 : good false 0 (pref false [0,0,2,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000200200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000200202
theorem R00020021 : good false 0 (pref false [0,0,2,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000200211
  · change good false 0 (step (pref false [0,0,2,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000200212
theorem R0002000 : good false 0 (pref false [0,0,2,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00020000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00020002
theorem R0002002 : good false 0 (pref false [0,0,2,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00020020
  · change good false 0 (step (pref false [0,0,2,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00020021
  · exact (hk (by decide)).elim
theorem R000200 : good false 0 (pref false [0,0,2,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,2,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0002000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,2,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0002002
end Ribbon5Owner
