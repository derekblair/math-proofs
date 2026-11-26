import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R020002000 : good false 2 (pref false [2,0,0,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R020002002 : good false 2 (pref false [2,0,0,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R020002020 : good false 2 (pref false [2,0,0,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R020002021 : good false 2 (pref false [2,0,0,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R020002111 : good false 2 (pref false [2,0,0,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R020002112 : good false 2 (pref false [2,0,0,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R020002120 : good false 2 (pref false [2,0,0,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R020002121 : good false 2 (pref false [2,0,0,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R02000200 : good false 2 (pref false [2,0,0,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020002000
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020002002
theorem R02000202 : good false 2 (pref false [2,0,0,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020002020
  · change good false 2 (step (pref false [2,0,0,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020002021
  · exact (hk (by decide)).elim
theorem R02000211 : good false 2 (pref false [2,0,0,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020002111
  · change good false 2 (step (pref false [2,0,0,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020002112
theorem R02000212 : good false 2 (pref false [2,0,0,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020002120
  · change good false 2 (step (pref false [2,0,0,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020002121
  · exact (hk (by decide)).elim
theorem R0200020 : good false 2 (pref false [2,0,0,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02000200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02000202
theorem R0200021 : good false 2 (pref false [2,0,0,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02000211
  · change good false 2 (step (pref false [2,0,0,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02000212
theorem R020002 : good false 2 (pref false [2,0,0,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0200020
  · change good false 2 (step (pref false [2,0,0,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0200021
  · exact (hk (by decide)).elim
end Ribbon5Owner
