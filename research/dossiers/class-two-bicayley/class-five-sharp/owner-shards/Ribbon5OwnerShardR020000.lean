import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R020000000 : good false 2 (pref false [2,0,0,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R020000002 : good false 2 (pref false [2,0,0,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R020000020 : good false 2 (pref false [2,0,0,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R020000021 : good false 2 (pref false [2,0,0,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R020000200 : good false 2 (pref false [2,0,0,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R020000202 : good false 2 (pref false [2,0,0,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R020000211 : good false 2 (pref false [2,0,0,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R020000212 : good false 2 (pref false [2,0,0,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R02000000 : good false 2 (pref false [2,0,0,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020000000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020000002
theorem R02000002 : good false 2 (pref false [2,0,0,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020000020
  · change good false 2 (step (pref false [2,0,0,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020000021
  · exact (hk (by decide)).elim
theorem R02000020 : good false 2 (pref false [2,0,0,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020000200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020000202
theorem R02000021 : good false 2 (pref false [2,0,0,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020000211
  · change good false 2 (step (pref false [2,0,0,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020000212
theorem R0200000 : good false 2 (pref false [2,0,0,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02000000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02000002
theorem R0200002 : good false 2 (pref false [2,0,0,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02000020
  · change good false 2 (step (pref false [2,0,0,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02000021
  · exact (hk (by decide)).elim
theorem R020000 : good false 2 (pref false [2,0,0,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0200000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0200002
end Ribbon5Owner
