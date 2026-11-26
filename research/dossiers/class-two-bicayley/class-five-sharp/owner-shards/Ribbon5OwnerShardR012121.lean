import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R012121111 : good false 1 (pref false [1,2,1,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R012121112 : good false 1 (pref false [1,2,1,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R012121120 : good false 1 (pref false [1,2,1,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R012121121 : good false 1 (pref false [1,2,1,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R012121200 : good false 1 (pref false [1,2,1,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R012121202 : good false 1 (pref false [1,2,1,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R012121211 : good false 1 (pref false [1,2,1,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R012121212 : good false 1 (pref false [1,2,1,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R01212111 : good false 1 (pref false [1,2,1,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012121111
  · change good false 1 (step (pref false [1,2,1,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012121112
theorem R01212112 : good false 1 (pref false [1,2,1,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012121120
  · change good false 1 (step (pref false [1,2,1,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012121121
  · exact (hk (by decide)).elim
theorem R01212120 : good false 1 (pref false [1,2,1,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012121200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012121202
theorem R01212121 : good false 1 (pref false [1,2,1,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012121211
  · change good false 1 (step (pref false [1,2,1,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012121212
theorem R0121211 : good false 1 (pref false [1,2,1,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01212111
  · change good false 1 (step (pref false [1,2,1,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01212112
theorem R0121212 : good false 1 (pref false [1,2,1,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01212120
  · change good false 1 (step (pref false [1,2,1,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01212121
  · exact (hk (by decide)).elim
theorem R012121 : good false 1 (pref false [1,2,1,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0121211
  · change good false 1 (step (pref false [1,2,1,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0121212
end Ribbon5Owner
