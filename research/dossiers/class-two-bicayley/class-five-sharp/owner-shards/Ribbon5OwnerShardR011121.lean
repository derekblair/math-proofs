import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R011121111 : good false 1 (pref false [1,1,1,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R011121112 : good false 1 (pref false [1,1,1,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R011121120 : good false 1 (pref false [1,1,1,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R011121121 : good false 1 (pref false [1,1,1,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R011121200 : good false 1 (pref false [1,1,1,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R011121202 : good false 1 (pref false [1,1,1,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R011121211 : good false 1 (pref false [1,1,1,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R011121212 : good false 1 (pref false [1,1,1,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R01112111 : good false 1 (pref false [1,1,1,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011121111
  · change good false 1 (step (pref false [1,1,1,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011121112
theorem R01112112 : good false 1 (pref false [1,1,1,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011121120
  · change good false 1 (step (pref false [1,1,1,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011121121
  · exact (hk (by decide)).elim
theorem R01112120 : good false 1 (pref false [1,1,1,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R011121200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011121202
theorem R01112121 : good false 1 (pref false [1,1,1,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R011121211
  · change good false 1 (step (pref false [1,1,1,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R011121212
theorem R0111211 : good false 1 (pref false [1,1,1,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01112111
  · change good false 1 (step (pref false [1,1,1,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01112112
theorem R0111212 : good false 1 (pref false [1,1,1,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,1,1,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01112120
  · change good false 1 (step (pref false [1,1,1,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01112121
  · exact (hk (by decide)).elim
theorem R011121 : good false 1 (pref false [1,1,1,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,1,1,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0111211
  · change good false 1 (step (pref false [1,1,1,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0111212
end Ribbon5Owner
