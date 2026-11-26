import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R020020000 : good false 2 (pref false [2,0,0,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R020020002 : good false 2 (pref false [2,0,0,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R020020020 : good false 2 (pref false [2,0,0,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R020020021 : good false 2 (pref false [2,0,0,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R020020200 : good false 2 (pref false [2,0,0,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R020020202 : good false 2 (pref false [2,0,0,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R020020211 : good false 2 (pref false [2,0,0,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R020020212 : good false 2 (pref false [2,0,0,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R02002000 : good false 2 (pref false [2,0,0,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020020000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020020002
theorem R02002002 : good false 2 (pref false [2,0,0,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020020020
  · change good false 2 (step (pref false [2,0,0,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020020021
  · exact (hk (by decide)).elim
theorem R02002020 : good false 2 (pref false [2,0,0,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020020200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020020202
theorem R02002021 : good false 2 (pref false [2,0,0,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020020211
  · change good false 2 (step (pref false [2,0,0,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020020212
theorem R0200200 : good false 2 (pref false [2,0,0,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02002000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02002002
theorem R0200202 : good false 2 (pref false [2,0,0,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02002020
  · change good false 2 (step (pref false [2,0,0,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02002021
  · exact (hk (by decide)).elim
theorem R020020 : good false 2 (pref false [2,0,0,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0200200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0200202
end Ribbon5Owner
