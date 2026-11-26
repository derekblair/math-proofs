import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R000021111 : good false 0 (pref false [0,0,0,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R000021112 : good false 0 (pref false [0,0,0,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R000021120 : good false 0 (pref false [0,0,0,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R000021121 : good false 0 (pref false [0,0,0,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R000021200 : good false 0 (pref false [0,0,0,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R000021202 : good false 0 (pref false [0,0,0,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R000021211 : good false 0 (pref false [0,0,0,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R000021212 : good false 0 (pref false [0,0,0,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R00002111 : good false 0 (pref false [0,0,0,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000021111
  · change good false 0 (step (pref false [0,0,0,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000021112
theorem R00002112 : good false 0 (pref false [0,0,0,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000021120
  · change good false 0 (step (pref false [0,0,0,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000021121
  · exact (hk (by decide)).elim
theorem R00002120 : good false 0 (pref false [0,0,0,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R000021200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000021202
theorem R00002121 : good false 0 (pref false [0,0,0,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R000021211
  · change good false 0 (step (pref false [0,0,0,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R000021212
theorem R0000211 : good false 0 (pref false [0,0,0,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00002111
  · change good false 0 (step (pref false [0,0,0,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00002112
theorem R0000212 : good false 0 (pref false [0,0,0,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,0,0,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00002120
  · change good false 0 (step (pref false [0,0,0,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00002121
  · exact (hk (by decide)).elim
theorem R000021 : good false 0 (pref false [0,0,0,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,0,0,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0000211
  · change good false 0 (step (pref false [0,0,0,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0000212
end Ribbon5Owner
