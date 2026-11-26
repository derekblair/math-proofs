import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R002121111 : good false 0 (pref false [0,2,1,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R002121112 : good false 0 (pref false [0,2,1,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R002121120 : good false 0 (pref false [0,2,1,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R002121121 : good false 0 (pref false [0,2,1,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R002121200 : good false 0 (pref false [0,2,1,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R002121202 : good false 0 (pref false [0,2,1,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R002121211 : good false 0 (pref false [0,2,1,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R002121212 : good false 0 (pref false [0,2,1,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R00212111 : good false 0 (pref false [0,2,1,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002121111
  · change good false 0 (step (pref false [0,2,1,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002121112
theorem R00212112 : good false 0 (pref false [0,2,1,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002121120
  · change good false 0 (step (pref false [0,2,1,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002121121
  · exact (hk (by decide)).elim
theorem R00212120 : good false 0 (pref false [0,2,1,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002121200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002121202
theorem R00212121 : good false 0 (pref false [0,2,1,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002121211
  · change good false 0 (step (pref false [0,2,1,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002121212
theorem R0021211 : good false 0 (pref false [0,2,1,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00212111
  · change good false 0 (step (pref false [0,2,1,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00212112
theorem R0021212 : good false 0 (pref false [0,2,1,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,1,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00212120
  · change good false 0 (step (pref false [0,2,1,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00212121
  · exact (hk (by decide)).elim
theorem R002121 : good false 0 (pref false [0,2,1,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,1,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0021211
  · change good false 0 (step (pref false [0,2,1,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0021212
end Ribbon5Owner
