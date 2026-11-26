import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R021112000 : good false 2 (pref false [2,1,1,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R021112002 : good false 2 (pref false [2,1,1,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R021112020 : good false 2 (pref false [2,1,1,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R021112021 : good false 2 (pref false [2,1,1,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R021112111 : good false 2 (pref false [2,1,1,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R021112112 : good false 2 (pref false [2,1,1,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R021112120 : good false 2 (pref false [2,1,1,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R021112121 : good false 2 (pref false [2,1,1,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R02111200 : good false 2 (pref false [2,1,1,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021112000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021112002
theorem R02111202 : good false 2 (pref false [2,1,1,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021112020
  · change good false 2 (step (pref false [2,1,1,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021112021
  · exact (hk (by decide)).elim
theorem R02111211 : good false 2 (pref false [2,1,1,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021112111
  · change good false 2 (step (pref false [2,1,1,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021112112
theorem R02111212 : good false 2 (pref false [2,1,1,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021112120
  · change good false 2 (step (pref false [2,1,1,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021112121
  · exact (hk (by decide)).elim
theorem R0211120 : good false 2 (pref false [2,1,1,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02111200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02111202
theorem R0211121 : good false 2 (pref false [2,1,1,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02111211
  · change good false 2 (step (pref false [2,1,1,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02111212
theorem R021112 : good false 2 (pref false [2,1,1,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0211120
  · change good false 2 (step (pref false [2,1,1,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0211121
  · exact (hk (by decide)).elim
end Ribbon5Owner
