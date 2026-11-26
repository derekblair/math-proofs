import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R011202000 : good false 1 (pref false [1,1,2,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R011202002 : good false 1 (pref false [1,1,2,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R011202020 : good false 1 (pref false [1,1,2,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R011202021 : good false 1 (pref false [1,1,2,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R011202111 : good false 1 (pref false [1,1,2,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R011202112 : good false 1 (pref false [1,1,2,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R011202120 : good false 1 (pref false [1,1,2,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R011202121 : good false 1 (pref false [1,1,2,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R01120200 : good false 1 (pref false [1,1,2,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011202000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011202002
theorem R01120202 : good false 1 (pref false [1,1,2,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011202020
  · change good false 1 (step (pref false [1,1,2,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011202021
  · exact (hk (by decide)).elim
theorem R01120211 : good false 1 (pref false [1,1,2,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011202111
  · change good false 1 (step (pref false [1,1,2,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011202112
theorem R01120212 : good false 1 (pref false [1,1,2,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011202120
  · change good false 1 (step (pref false [1,1,2,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011202121
  · exact (hk (by decide)).elim
theorem R0112020 : good false 1 (pref false [1,1,2,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01120200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01120202
theorem R0112021 : good false 1 (pref false [1,1,2,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,2,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01120211
  · change good false 1 (step (pref false [1,1,2,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01120212
theorem R011202 : good false 1 (pref false [1,1,2,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,2,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0112020
  · change good false 1 (step (pref false [1,1,2,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0112021
  · exact (hk (by decide)).elim
end Ribbon5Owner
