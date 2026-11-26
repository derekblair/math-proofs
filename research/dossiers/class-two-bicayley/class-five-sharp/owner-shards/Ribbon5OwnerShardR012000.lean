import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R012000000 : good false 1 (pref false [1,2,0,0,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R012000002 : good false 1 (pref false [1,2,0,0,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R012000020 : good false 1 (pref false [1,2,0,0,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R012000021 : good false 1 (pref false [1,2,0,0,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R012000200 : good false 1 (pref false [1,2,0,0,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R012000202 : good false 1 (pref false [1,2,0,0,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R012000211 : good false 1 (pref false [1,2,0,0,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R012000212 : good false 1 (pref false [1,2,0,0,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R01200000 : good false 1 (pref false [1,2,0,0,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012000000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,0,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012000002
theorem R01200002 : good false 1 (pref false [1,2,0,0,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012000020
  · change good false 1 (step (pref false [1,2,0,0,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012000021
  · exact (hk (by decide)).elim
theorem R01200020 : good false 1 (pref false [1,2,0,0,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012000200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,0,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012000202
theorem R01200021 : good false 1 (pref false [1,2,0,0,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,0,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012000211
  · change good false 1 (step (pref false [1,2,0,0,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012000212
theorem R0120000 : good false 1 (pref false [1,2,0,0,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01200000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,0,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01200002
theorem R0120002 : good false 1 (pref false [1,2,0,0,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01200020
  · change good false 1 (step (pref false [1,2,0,0,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01200021
  · exact (hk (by decide)).elim
theorem R012000 : good false 1 (pref false [1,2,0,0,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0120000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,0,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0120002
end Ribbon5Owner
