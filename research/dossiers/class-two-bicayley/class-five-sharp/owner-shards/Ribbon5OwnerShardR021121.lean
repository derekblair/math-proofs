import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R021121111 : good false 2 (pref false [2,1,1,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R021121112 : good false 2 (pref false [2,1,1,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R021121120 : good false 2 (pref false [2,1,1,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R021121121 : good false 2 (pref false [2,1,1,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R021121200 : good false 2 (pref false [2,1,1,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R021121202 : good false 2 (pref false [2,1,1,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R021121211 : good false 2 (pref false [2,1,1,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R021121212 : good false 2 (pref false [2,1,1,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R02112111 : good false 2 (pref false [2,1,1,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021121111
  · change good false 2 (step (pref false [2,1,1,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021121112
theorem R02112112 : good false 2 (pref false [2,1,1,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021121120
  · change good false 2 (step (pref false [2,1,1,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021121121
  · exact (hk (by decide)).elim
theorem R02112120 : good false 2 (pref false [2,1,1,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021121200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021121202
theorem R02112121 : good false 2 (pref false [2,1,1,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021121211
  · change good false 2 (step (pref false [2,1,1,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021121212
theorem R0211211 : good false 2 (pref false [2,1,1,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02112111
  · change good false 2 (step (pref false [2,1,1,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02112112
theorem R0211212 : good false 2 (pref false [2,1,1,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02112120
  · change good false 2 (step (pref false [2,1,1,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02112121
  · exact (hk (by decide)).elim
theorem R021121 : good false 2 (pref false [2,1,1,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0211211
  · change good false 2 (step (pref false [2,1,1,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0211212
end Ribbon5Owner
