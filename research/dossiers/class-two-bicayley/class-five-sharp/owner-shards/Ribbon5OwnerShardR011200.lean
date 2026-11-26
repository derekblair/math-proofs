import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R011200000 : good false 1 (pref false [1,1,2,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R011200002 : good false 1 (pref false [1,1,2,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R011200020 : good false 1 (pref false [1,1,2,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R011200021 : good false 1 (pref false [1,1,2,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R011200200 : good false 1 (pref false [1,1,2,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R011200202 : good false 1 (pref false [1,1,2,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R011200211 : good false 1 (pref false [1,1,2,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R011200212 : good false 1 (pref false [1,1,2,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R01120000 : good false 1 (pref false [1,1,2,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011200000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011200002
theorem R01120002 : good false 1 (pref false [1,1,2,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011200020
  · change good false 1 (step (pref false [1,1,2,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011200021
  · exact (hk (by decide)).elim
theorem R01120020 : good false 1 (pref false [1,1,2,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011200200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011200202
theorem R01120021 : good false 1 (pref false [1,1,2,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011200211
  · change good false 1 (step (pref false [1,1,2,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011200212
theorem R0112000 : good false 1 (pref false [1,1,2,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01120000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01120002
theorem R0112002 : good false 1 (pref false [1,1,2,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01120020
  · change good false 1 (step (pref false [1,1,2,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01120021
  · exact (hk (by decide)).elim
theorem R011200 : good false 1 (pref false [1,1,2,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0112000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0112002
end Ribbon5Owner
