import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R012021111 : good false 1 (pref false [1,2,0,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R012021112 : good false 1 (pref false [1,2,0,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R012021120 : good false 1 (pref false [1,2,0,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R012021121 : good false 1 (pref false [1,2,0,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R012021200 : good false 1 (pref false [1,2,0,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R012021202 : good false 1 (pref false [1,2,0,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R012021211 : good false 1 (pref false [1,2,0,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R012021212 : good false 1 (pref false [1,2,0,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R01202111 : good false 1 (pref false [1,2,0,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012021111
  · change good false 1 (step (pref false [1,2,0,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012021112
theorem R01202112 : good false 1 (pref false [1,2,0,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012021120
  · change good false 1 (step (pref false [1,2,0,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012021121
  · exact (hk (by decide)).elim
theorem R01202120 : good false 1 (pref false [1,2,0,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012021200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012021202
theorem R01202121 : good false 1 (pref false [1,2,0,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012021211
  · change good false 1 (step (pref false [1,2,0,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012021212
theorem R0120211 : good false 1 (pref false [1,2,0,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01202111
  · change good false 1 (step (pref false [1,2,0,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01202112
theorem R0120212 : good false 1 (pref false [1,2,0,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01202120
  · change good false 1 (step (pref false [1,2,0,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01202121
  · exact (hk (by decide)).elim
theorem R012021 : good false 1 (pref false [1,2,0,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0120211
  · change good false 1 (step (pref false [1,2,0,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0120212
end Ribbon5Owner
