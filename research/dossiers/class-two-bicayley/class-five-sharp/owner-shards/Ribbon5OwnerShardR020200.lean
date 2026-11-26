import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R020200000 : good false 2 (pref false [2,0,2,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R020200002 : good false 2 (pref false [2,0,2,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R020200020 : good false 2 (pref false [2,0,2,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R020200021 : good false 2 (pref false [2,0,2,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R020200200 : good false 2 (pref false [2,0,2,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R020200202 : good false 2 (pref false [2,0,2,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R020200211 : good false 2 (pref false [2,0,2,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R020200212 : good false 2 (pref false [2,0,2,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R02020000 : good false 2 (pref false [2,0,2,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020200000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020200002
theorem R02020002 : good false 2 (pref false [2,0,2,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020200020
  · change good false 2 (step (pref false [2,0,2,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020200021
  · exact (hk (by decide)).elim
theorem R02020020 : good false 2 (pref false [2,0,2,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020200200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020200202
theorem R02020021 : good false 2 (pref false [2,0,2,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020200211
  · change good false 2 (step (pref false [2,0,2,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020200212
theorem R0202000 : good false 2 (pref false [2,0,2,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02020000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02020002
theorem R0202002 : good false 2 (pref false [2,0,2,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02020020
  · change good false 2 (step (pref false [2,0,2,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02020021
  · exact (hk (by decide)).elim
theorem R020200 : good false 2 (pref false [2,0,2,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0202000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0202002
end Ribbon5Owner
