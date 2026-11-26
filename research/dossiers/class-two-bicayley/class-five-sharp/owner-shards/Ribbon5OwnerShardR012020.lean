import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R012020000 : good false 1 (pref false [1,2,0,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R012020002 : good false 1 (pref false [1,2,0,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R012020020 : good false 1 (pref false [1,2,0,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R012020021 : good false 1 (pref false [1,2,0,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R012020200 : good false 1 (pref false [1,2,0,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R012020202 : good false 1 (pref false [1,2,0,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R012020211 : good false 1 (pref false [1,2,0,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R012020212 : good false 1 (pref false [1,2,0,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R01202000 : good false 1 (pref false [1,2,0,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012020000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012020002
theorem R01202002 : good false 1 (pref false [1,2,0,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012020020
  · change good false 1 (step (pref false [1,2,0,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012020021
  · exact (hk (by decide)).elim
theorem R01202020 : good false 1 (pref false [1,2,0,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012020200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012020202
theorem R01202021 : good false 1 (pref false [1,2,0,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012020211
  · change good false 1 (step (pref false [1,2,0,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012020212
theorem R0120200 : good false 1 (pref false [1,2,0,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01202000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01202002
theorem R0120202 : good false 1 (pref false [1,2,0,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01202020
  · change good false 1 (step (pref false [1,2,0,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01202021
  · exact (hk (by decide)).elim
theorem R012020 : good false 1 (pref false [1,2,0,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0120200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0120202
end Ribbon5Owner
