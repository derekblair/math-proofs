import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R021202000 : good false 2 (pref false [2,1,2,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R021202002 : good false 2 (pref false [2,1,2,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R021202020 : good false 2 (pref false [2,1,2,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R021202021 : good false 2 (pref false [2,1,2,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R021202111 : good false 2 (pref false [2,1,2,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R021202112 : good false 2 (pref false [2,1,2,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R021202120 : good false 2 (pref false [2,1,2,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R021202121 : good false 2 (pref false [2,1,2,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R02120200 : good false 2 (pref false [2,1,2,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021202000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021202002
theorem R02120202 : good false 2 (pref false [2,1,2,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021202020
  · change good false 2 (step (pref false [2,1,2,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021202021
  · exact (hk (by decide)).elim
theorem R02120211 : good false 2 (pref false [2,1,2,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021202111
  · change good false 2 (step (pref false [2,1,2,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021202112
theorem R02120212 : good false 2 (pref false [2,1,2,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021202120
  · change good false 2 (step (pref false [2,1,2,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021202121
  · exact (hk (by decide)).elim
theorem R0212020 : good false 2 (pref false [2,1,2,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02120200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02120202
theorem R0212021 : good false 2 (pref false [2,1,2,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,2,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02120211
  · change good false 2 (step (pref false [2,1,2,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02120212
theorem R021202 : good false 2 (pref false [2,1,2,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,2,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0212020
  · change good false 2 (step (pref false [2,1,2,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0212021
  · exact (hk (by decide)).elim
end Ribbon5Owner
