import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R020021111 : good false 2 (pref false [2,0,0,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R020021112 : good false 2 (pref false [2,0,0,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R020021120 : good false 2 (pref false [2,0,0,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R020021121 : good false 2 (pref false [2,0,0,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R020021200 : good false 2 (pref false [2,0,0,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R020021202 : good false 2 (pref false [2,0,0,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R020021211 : good false 2 (pref false [2,0,0,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R020021212 : good false 2 (pref false [2,0,0,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R02002111 : good false 2 (pref false [2,0,0,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020021111
  · change good false 2 (step (pref false [2,0,0,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020021112
theorem R02002112 : good false 2 (pref false [2,0,0,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020021120
  · change good false 2 (step (pref false [2,0,0,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020021121
  · exact (hk (by decide)).elim
theorem R02002120 : good false 2 (pref false [2,0,0,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R020021200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020021202
theorem R02002121 : good false 2 (pref false [2,0,0,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R020021211
  · change good false 2 (step (pref false [2,0,0,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R020021212
theorem R0200211 : good false 2 (pref false [2,0,0,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02002111
  · change good false 2 (step (pref false [2,0,0,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02002112
theorem R0200212 : good false 2 (pref false [2,0,0,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,0,0,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02002120
  · change good false 2 (step (pref false [2,0,0,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02002121
  · exact (hk (by decide)).elim
theorem R020021 : good false 2 (pref false [2,0,0,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,0,0,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0200211
  · change good false 2 (step (pref false [2,0,0,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0200212
end Ribbon5Owner
