import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R002120000 : good false 0 (pref false [0,2,1,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R002120002 : good false 0 (pref false [0,2,1,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R002120020 : good false 0 (pref false [0,2,1,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R002120021 : good false 0 (pref false [0,2,1,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R002120200 : good false 0 (pref false [0,2,1,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R002120202 : good false 0 (pref false [0,2,1,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R002120211 : good false 0 (pref false [0,2,1,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R002120212 : good false 0 (pref false [0,2,1,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R00212000 : good false 0 (pref false [0,2,1,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002120000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002120002
theorem R00212002 : good false 0 (pref false [0,2,1,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002120020
  · change good false 0 (step (pref false [0,2,1,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002120021
  · exact (hk (by decide)).elim
theorem R00212020 : good false 0 (pref false [0,2,1,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002120200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002120202
theorem R00212021 : good false 0 (pref false [0,2,1,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002120211
  · change good false 0 (step (pref false [0,2,1,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002120212
theorem R0021200 : good false 0 (pref false [0,2,1,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00212000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00212002
theorem R0021202 : good false 0 (pref false [0,2,1,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00212020
  · change good false 0 (step (pref false [0,2,1,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00212021
  · exact (hk (by decide)).elim
theorem R002120 : good false 0 (pref false [0,2,1,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0021200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0021202
end Ribbon5Owner
