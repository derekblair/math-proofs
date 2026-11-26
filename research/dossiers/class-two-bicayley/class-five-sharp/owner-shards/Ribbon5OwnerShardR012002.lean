import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R012002000 : good false 1 (pref false [1,2,0,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R012002002 : good false 1 (pref false [1,2,0,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R012002020 : good false 1 (pref false [1,2,0,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R012002021 : good false 1 (pref false [1,2,0,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R012002111 : good false 1 (pref false [1,2,0,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R012002112 : good false 1 (pref false [1,2,0,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R012002120 : good false 1 (pref false [1,2,0,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R012002121 : good false 1 (pref false [1,2,0,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R01200200 : good false 1 (pref false [1,2,0,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012002000
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012002002
theorem R01200202 : good false 1 (pref false [1,2,0,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012002020
  · change good false 1 (step (pref false [1,2,0,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012002021
  · exact (hk (by decide)).elim
theorem R01200211 : good false 1 (pref false [1,2,0,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012002111
  · change good false 1 (step (pref false [1,2,0,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012002112
theorem R01200212 : good false 1 (pref false [1,2,0,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012002120
  · change good false 1 (step (pref false [1,2,0,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012002121
  · exact (hk (by decide)).elim
theorem R0120020 : good false 1 (pref false [1,2,0,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01200200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01200202
theorem R0120021 : good false 1 (pref false [1,2,0,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,0,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01200211
  · change good false 1 (step (pref false [1,2,0,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01200212
theorem R012002 : good false 1 (pref false [1,2,0,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,0,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0120020
  · change good false 1 (step (pref false [1,2,0,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0120021
  · exact (hk (by decide)).elim
end Ribbon5Owner
