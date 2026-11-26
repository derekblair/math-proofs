import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R021111111 : good false 2 (pref false [2,1,1,1,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R021111112 : good false 2 (pref false [2,1,1,1,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R021111120 : good false 2 (pref false [2,1,1,1,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R021111121 : good false 2 (pref false [2,1,1,1,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R021111200 : good false 2 (pref false [2,1,1,1,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R021111202 : good false 2 (pref false [2,1,1,1,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R021111211 : good false 2 (pref false [2,1,1,1,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R021111212 : good false 2 (pref false [2,1,1,1,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R02111111 : good false 2 (pref false [2,1,1,1,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,1,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021111111
  · change good false 2 (step (pref false [2,1,1,1,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021111112
theorem R02111112 : good false 2 (pref false [2,1,1,1,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,1,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021111120
  · change good false 2 (step (pref false [2,1,1,1,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021111121
  · exact (hk (by decide)).elim
theorem R02111120 : good false 2 (pref false [2,1,1,1,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,1,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R021111200
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,1,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021111202
theorem R02111121 : good false 2 (pref false [2,1,1,1,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,1,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R021111211
  · change good false 2 (step (pref false [2,1,1,1,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R021111212
theorem R0211111 : good false 2 (pref false [2,1,1,1,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,1,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02111111
  · change good false 2 (step (pref false [2,1,1,1,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R02111112
theorem R0211112 : good false 2 (pref false [2,1,1,1,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 2 (step (pref false [2,1,1,1,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R02111120
  · change good false 2 (step (pref false [2,1,1,1,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R02111121
  · exact (hk (by decide)).elim
theorem R021111 : good false 2 (pref false [2,1,1,1,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 2 (step (pref false [2,1,1,1,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0211111
  · change good false 2 (step (pref false [2,1,1,1,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0211112
end Ribbon5Owner
