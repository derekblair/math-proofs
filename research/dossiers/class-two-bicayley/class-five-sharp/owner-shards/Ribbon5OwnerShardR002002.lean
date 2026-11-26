import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R002002000 : good false 0 (pref false [0,2,0,0,2,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R002002002 : good false 0 (pref false [0,2,0,0,2,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R002002020 : good false 0 (pref false [0,2,0,0,2,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R002002021 : good false 0 (pref false [0,2,0,0,2,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R002002111 : good false 0 (pref false [0,2,0,0,2,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R002002112 : good false 0 (pref false [0,2,0,0,2,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R002002120 : good false 0 (pref false [0,2,0,0,2,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R002002121 : good false 0 (pref false [0,2,0,0,2,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R00200200 : good false 0 (pref false [0,2,0,0,2,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0,2,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002002000
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,0,2,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002002002
theorem R00200202 : good false 0 (pref false [0,2,0,0,2,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0,2,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002002020
  · change good false 0 (step (pref false [0,2,0,0,2,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002002021
  · exact (hk (by decide)).elim
theorem R00200211 : good false 0 (pref false [0,2,0,0,2,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,0,2,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002002111
  · change good false 0 (step (pref false [0,2,0,0,2,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R002002112
theorem R00200212 : good false 0 (pref false [0,2,0,0,2,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0,2,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R002002120
  · change good false 0 (step (pref false [0,2,0,0,2,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R002002121
  · exact (hk (by decide)).elim
theorem R0020020 : good false 0 (pref false [0,2,0,0,2,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0,2,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R00200200
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,0,2,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00200202
theorem R0020021 : good false 0 (pref false [0,2,0,0,2,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good false 0 (step (pref false [0,2,0,0,2,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R00200211
  · change good false 0 (step (pref false [0,2,0,0,2,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R00200212
theorem R002002 : good false 0 (pref false [0,2,0,0,2]) 2 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good false 0 (step (pref false [0,2,0,0,2]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R0020020
  · change good false 0 (step (pref false [0,2,0,0,2]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R0020021
  · exact (hk (by decide)).elim
end Ribbon5Owner
