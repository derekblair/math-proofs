import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R021200000 : good false 2 (pref false [2,1,2,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R021200002 : good false 2 (pref false [2,1,2,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R021200020 : good false 2 (pref false [2,1,2,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R021200021 : good false 2 (pref false [2,1,2,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R021200200 : good false 2 (pref false [2,1,2,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R021200202 : good false 2 (pref false [2,1,2,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R021200211 : good false 2 (pref false [2,1,2,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R021200212 : good false 2 (pref false [2,1,2,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R02120000 : good false 2 (pref false [2,1,2,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021200000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021200002
theorem R02120002 : good false 2 (pref false [2,1,2,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021200020
  · change good false 2 (step (pref false [2,1,2,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021200021
  · exact (hk (by decide)).elim
theorem R02120020 : good false 2 (pref false [2,1,2,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021200200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021200202
theorem R02120021 : good false 2 (pref false [2,1,2,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021200211
  · change good false 2 (step (pref false [2,1,2,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021200212
theorem R0212000 : good false 2 (pref false [2,1,2,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02120000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02120002
theorem R0212002 : good false 2 (pref false [2,1,2,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02120020
  · change good false 2 (step (pref false [2,1,2,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02120021
  · exact (hk (by decide)).elim
theorem R021200 : good false 2 (pref false [2,1,2,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0212000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0212002
end Ribbon5Owner
