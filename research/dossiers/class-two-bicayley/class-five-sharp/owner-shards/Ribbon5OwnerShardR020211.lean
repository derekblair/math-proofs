import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R020211111 : good false 2 (pref false [2,0,2,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R020211112 : good false 2 (pref false [2,0,2,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R020211120 : good false 2 (pref false [2,0,2,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R020211121 : good false 2 (pref false [2,0,2,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R020211200 : good false 2 (pref false [2,0,2,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R020211202 : good false 2 (pref false [2,0,2,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R020211211 : good false 2 (pref false [2,0,2,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R020211212 : good false 2 (pref false [2,0,2,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R02021111 : good false 2 (pref false [2,0,2,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020211111
  · change good false 2 (step (pref false [2,0,2,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020211112
theorem R02021112 : good false 2 (pref false [2,0,2,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020211120
  · change good false 2 (step (pref false [2,0,2,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020211121
  · exact (hk (by decide)).elim
theorem R02021120 : good false 2 (pref false [2,0,2,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020211200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020211202
theorem R02021121 : good false 2 (pref false [2,0,2,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020211211
  · change good false 2 (step (pref false [2,0,2,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020211212
theorem R0202111 : good false 2 (pref false [2,0,2,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02021111
  · change good false 2 (step (pref false [2,0,2,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02021112
theorem R0202112 : good false 2 (pref false [2,0,2,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02021120
  · change good false 2 (step (pref false [2,0,2,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02021121
  · exact (hk (by decide)).elim
theorem R020211 : good false 2 (pref false [2,0,2,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0202111
  · change good false 2 (step (pref false [2,0,2,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0202112
end Ribbon5Owner
