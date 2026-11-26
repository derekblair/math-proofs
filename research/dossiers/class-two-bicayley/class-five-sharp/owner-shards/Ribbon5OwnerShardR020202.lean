import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R020202000 : good false 2 (pref false [2,0,2,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R020202002 : good false 2 (pref false [2,0,2,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R020202020 : good false 2 (pref false [2,0,2,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R020202021 : good false 2 (pref false [2,0,2,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R020202111 : good false 2 (pref false [2,0,2,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R020202112 : good false 2 (pref false [2,0,2,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R020202120 : good false 2 (pref false [2,0,2,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R020202121 : good false 2 (pref false [2,0,2,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R02020200 : good false 2 (pref false [2,0,2,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020202000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020202002
theorem R02020202 : good false 2 (pref false [2,0,2,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020202020
  · change good false 2 (step (pref false [2,0,2,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020202021
  · exact (hk (by decide)).elim
theorem R02020211 : good false 2 (pref false [2,0,2,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020202111
  · change good false 2 (step (pref false [2,0,2,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020202112
theorem R02020212 : good false 2 (pref false [2,0,2,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020202120
  · change good false 2 (step (pref false [2,0,2,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020202121
  · exact (hk (by decide)).elim
theorem R0202020 : good false 2 (pref false [2,0,2,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02020200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02020202
theorem R0202021 : good false 2 (pref false [2,0,2,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,2,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02020211
  · change good false 2 (step (pref false [2,0,2,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02020212
theorem R020202 : good false 2 (pref false [2,0,2,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,2,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0202020
  · change good false 2 (step (pref false [2,0,2,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0202021
  · exact (hk (by decide)).elim
end Ribbon5Owner
