import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R002000000 : good false 0 (pref false [0,2,0,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R002000002 : good false 0 (pref false [0,2,0,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R002000020 : good false 0 (pref false [0,2,0,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R002000021 : good false 0 (pref false [0,2,0,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R002000200 : good false 0 (pref false [0,2,0,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R002000202 : good false 0 (pref false [0,2,0,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R002000211 : good false 0 (pref false [0,2,0,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R002000212 : good false 0 (pref false [0,2,0,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R00200000 : good false 0 (pref false [0,2,0,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002000000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002000002
theorem R00200002 : good false 0 (pref false [0,2,0,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002000020
  · change good false 0 (step (pref false [0,2,0,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002000021
  · exact (hk (by decide)).elim
theorem R00200020 : good false 0 (pref false [0,2,0,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002000200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002000202
theorem R00200021 : good false 0 (pref false [0,2,0,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002000211
  · change good false 0 (step (pref false [0,2,0,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002000212
theorem R0020000 : good false 0 (pref false [0,2,0,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00200000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00200002
theorem R0020002 : good false 0 (pref false [0,2,0,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00200020
  · change good false 0 (step (pref false [0,2,0,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00200021
  · exact (hk (by decide)).elim
theorem R002000 : good false 0 (pref false [0,2,0,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0020000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0020002
end Ribbon5Owner
