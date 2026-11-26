import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R002021111 : good false 0 (pref false [0,2,0,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R002021112 : good false 0 (pref false [0,2,0,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R002021120 : good false 0 (pref false [0,2,0,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R002021121 : good false 0 (pref false [0,2,0,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R002021200 : good false 0 (pref false [0,2,0,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R002021202 : good false 0 (pref false [0,2,0,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R002021211 : good false 0 (pref false [0,2,0,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R002021212 : good false 0 (pref false [0,2,0,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R00202111 : good false 0 (pref false [0,2,0,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002021111
  · change good false 0 (step (pref false [0,2,0,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002021112
theorem R00202112 : good false 0 (pref false [0,2,0,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002021120
  · change good false 0 (step (pref false [0,2,0,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002021121
  · exact (hk (by decide)).elim
theorem R00202120 : good false 0 (pref false [0,2,0,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002021200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002021202
theorem R00202121 : good false 0 (pref false [0,2,0,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002021211
  · change good false 0 (step (pref false [0,2,0,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002021212
theorem R0020211 : good false 0 (pref false [0,2,0,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00202111
  · change good false 0 (step (pref false [0,2,0,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00202112
theorem R0020212 : good false 0 (pref false [0,2,0,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00202120
  · change good false 0 (step (pref false [0,2,0,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00202121
  · exact (hk (by decide)).elim
theorem R002021 : good false 0 (pref false [0,2,0,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0020211
  · change good false 0 (step (pref false [0,2,0,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0020212
end Ribbon5Owner
