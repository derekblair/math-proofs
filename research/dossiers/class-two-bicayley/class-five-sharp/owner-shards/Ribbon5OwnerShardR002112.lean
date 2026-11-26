import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R002112000 : good false 0 (pref false [0,2,1,1,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R002112002 : good false 0 (pref false [0,2,1,1,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R002112020 : good false 0 (pref false [0,2,1,1,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R002112021 : good false 0 (pref false [0,2,1,1,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R002112111 : good false 0 (pref false [0,2,1,1,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R002112112 : good false 0 (pref false [0,2,1,1,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R002112120 : good false 0 (pref false [0,2,1,1,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R002112121 : good false 0 (pref false [0,2,1,1,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R00211200 : good false 0 (pref false [0,2,1,1,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,1,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002112000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,1,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002112002
theorem R00211202 : good false 0 (pref false [0,2,1,1,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,1,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002112020
  · change good false 0 (step (pref false [0,2,1,1,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002112021
  · exact (hk (by decide)).elim
theorem R00211211 : good false 0 (pref false [0,2,1,1,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,1,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002112111
  · change good false 0 (step (pref false [0,2,1,1,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002112112
theorem R00211212 : good false 0 (pref false [0,2,1,1,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,1,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002112120
  · change good false 0 (step (pref false [0,2,1,1,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002112121
  · exact (hk (by decide)).elim
theorem R0021120 : good false 0 (pref false [0,2,1,1,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,1,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00211200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,1,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00211202
theorem R0021121 : good false 0 (pref false [0,2,1,1,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,1,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00211211
  · change good false 0 (step (pref false [0,2,1,1,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00211212
theorem R002112 : good false 0 (pref false [0,2,1,1,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,1,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0021120
  · change good false 0 (step (pref false [0,2,1,1,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0021121
  · exact (hk (by decide)).elim
end Ribbon5Owner
