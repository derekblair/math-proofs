import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R121120000 : good true 2 (pref true [2,1,1,2,0,0,0,0]) 0 8 = true := by
  decide +kernel
theorem R121120002 : good true 2 (pref true [2,1,1,2,0,0,0,2]) 2 8 = true := by
  decide +kernel
theorem R121120020 : good true 2 (pref true [2,1,1,2,0,0,2,0]) 0 8 = true := by
  decide +kernel
theorem R121120021 : good true 2 (pref true [2,1,1,2,0,0,2,1]) 1 8 = true := by
  decide +kernel
theorem R121120200 : good true 2 (pref true [2,1,1,2,0,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R121120202 : good true 2 (pref true [2,1,1,2,0,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R121120211 : good true 2 (pref true [2,1,1,2,0,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R121120212 : good true 2 (pref true [2,1,1,2,0,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R12112000 : good true 2 (pref true [2,1,1,2,0,0,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,2,0,0,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121120000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,2,0,0,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121120002
theorem R12112002 : good true 2 (pref true [2,1,1,2,0,0,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,2,0,0,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121120020
  · change good true 2 (step (pref true [2,1,1,2,0,0,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121120021
  · exact (hk (by decide)).elim
theorem R12112020 : good true 2 (pref true [2,1,1,2,0,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,2,0,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121120200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,2,0,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121120202
theorem R12112021 : good true 2 (pref true [2,1,1,2,0,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,2,0,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121120211
  · change good true 2 (step (pref true [2,1,1,2,0,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121120212
theorem R1211200 : good true 2 (pref true [2,1,1,2,0,0]) 0 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,2,0,0]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12112000
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,2,0,0]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12112002
theorem R1211202 : good true 2 (pref true [2,1,1,2,0,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,2,0,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12112020
  · change good true 2 (step (pref true [2,1,1,2,0,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12112021
  · exact (hk (by decide)).elim
theorem R121120 : good true 2 (pref true [2,1,1,2,0]) 0 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,2,0]) 0) 0 10 = true
    rw [← pref_snoc]
    exact R1211200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,2,0]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1211202
end Ribbon5Owner
