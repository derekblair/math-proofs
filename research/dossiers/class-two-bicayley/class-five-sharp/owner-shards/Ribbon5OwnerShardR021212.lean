import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R021212000 : good false 2 (pref false [2,1,2,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R021212002 : good false 2 (pref false [2,1,2,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R021212020 : good false 2 (pref false [2,1,2,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R021212021 : good false 2 (pref false [2,1,2,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R021212111 : good false 2 (pref false [2,1,2,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R021212112 : good false 2 (pref false [2,1,2,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R021212120 : good false 2 (pref false [2,1,2,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R021212121 : good false 2 (pref false [2,1,2,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R02121200 : good false 2 (pref false [2,1,2,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021212000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021212002
theorem R02121202 : good false 2 (pref false [2,1,2,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021212020
  · change good false 2 (step (pref false [2,1,2,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021212021
  · exact (hk (by decide)).elim
theorem R02121211 : good false 2 (pref false [2,1,2,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021212111
  · change good false 2 (step (pref false [2,1,2,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021212112
theorem R02121212 : good false 2 (pref false [2,1,2,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021212120
  · change good false 2 (step (pref false [2,1,2,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021212121
  · exact (hk (by decide)).elim
theorem R0212120 : good false 2 (pref false [2,1,2,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02121200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02121202
theorem R0212121 : good false 2 (pref false [2,1,2,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02121211
  · change good false 2 (step (pref false [2,1,2,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02121212
theorem R021212 : good false 2 (pref false [2,1,2,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0212120
  · change good false 2 (step (pref false [2,1,2,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0212121
  · exact (hk (by decide)).elim
end Ribbon5Owner
