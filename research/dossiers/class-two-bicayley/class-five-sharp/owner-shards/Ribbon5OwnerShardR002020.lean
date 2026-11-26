import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R002020000 : good false 0 (pref false [0,2,0,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R002020002 : good false 0 (pref false [0,2,0,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R002020020 : good false 0 (pref false [0,2,0,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R002020021 : good false 0 (pref false [0,2,0,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R002020200 : good false 0 (pref false [0,2,0,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R002020202 : good false 0 (pref false [0,2,0,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R002020211 : good false 0 (pref false [0,2,0,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R002020212 : good false 0 (pref false [0,2,0,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R00202000 : good false 0 (pref false [0,2,0,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002020000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002020002
theorem R00202002 : good false 0 (pref false [0,2,0,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002020020
  · change good false 0 (step (pref false [0,2,0,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002020021
  · exact (hk (by decide)).elim
theorem R00202020 : good false 0 (pref false [0,2,0,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002020200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002020202
theorem R00202021 : good false 0 (pref false [0,2,0,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002020211
  · change good false 0 (step (pref false [0,2,0,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002020212
theorem R0020200 : good false 0 (pref false [0,2,0,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00202000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00202002
theorem R0020202 : good false 0 (pref false [0,2,0,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00202020
  · change good false 0 (step (pref false [0,2,0,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00202021
  · exact (hk (by decide)).elim
theorem R002020 : good false 0 (pref false [0,2,0,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0020200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R0020202
end Ribbon5Owner
