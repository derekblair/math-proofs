import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R012111111 : good false 1 (pref false [1,2,1,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R012111112 : good false 1 (pref false [1,2,1,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R012111120 : good false 1 (pref false [1,2,1,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R012111121 : good false 1 (pref false [1,2,1,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R012111200 : good false 1 (pref false [1,2,1,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R012111202 : good false 1 (pref false [1,2,1,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R012111211 : good false 1 (pref false [1,2,1,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R012111212 : good false 1 (pref false [1,2,1,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R01211111 : good false 1 (pref false [1,2,1,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012111111
  · change good false 1 (step (pref false [1,2,1,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012111112
theorem R01211112 : good false 1 (pref false [1,2,1,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012111120
  · change good false 1 (step (pref false [1,2,1,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012111121
  · exact (hk (by decide)).elim
theorem R01211120 : good false 1 (pref false [1,2,1,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R012111200
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012111202
theorem R01211121 : good false 1 (pref false [1,2,1,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R012111211
  · change good false 1 (step (pref false [1,2,1,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R012111212
theorem R0121111 : good false 1 (pref false [1,2,1,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01211111
  · change good false 1 (step (pref false [1,2,1,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R01211112
theorem R0121112 : good false 1 (pref false [1,2,1,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 1 (step (pref false [1,2,1,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R01211120
  · change good false 1 (step (pref false [1,2,1,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R01211121
  · exact (hk (by decide)).elim
theorem R012111 : good false 1 (pref false [1,2,1,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 1 (step (pref false [1,2,1,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0121111
  · change good false 1 (step (pref false [1,2,1,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0121112
end Ribbon5Owner
