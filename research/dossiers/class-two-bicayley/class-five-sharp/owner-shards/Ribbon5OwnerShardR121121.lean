import Ribbon5OwnerBase

namespace Ribbon5Owner
open Ribbon5Packed
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem R121121111 : good true 2 (pref true [2,1,1,2,1,1,1,1]) 1 8 = true := by
  decide +kernel
theorem R121121112 : good true 2 (pref true [2,1,1,2,1,1,1,2]) 2 8 = true := by
  decide +kernel
theorem R121121120 : good true 2 (pref true [2,1,1,2,1,1,2,0]) 0 8 = true := by
  decide +kernel
theorem R121121121 : good true 2 (pref true [2,1,1,2,1,1,2,1]) 1 8 = true := by
  decide +kernel
theorem R121121200 : good true 2 (pref true [2,1,1,2,1,2,0,0]) 0 8 = true := by
  decide +kernel
theorem R121121202 : good true 2 (pref true [2,1,1,2,1,2,0,2]) 2 8 = true := by
  decide +kernel
theorem R121121211 : good true 2 (pref true [2,1,1,2,1,2,1,1]) 1 8 = true := by
  decide +kernel
theorem R121121212 : good true 2 (pref true [2,1,1,2,1,2,1,2]) 2 8 = true := by
  decide +kernel
theorem R12112111 : good true 2 (pref true [2,1,1,2,1,1,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,2,1,1,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121121111
  · change good true 2 (step (pref true [2,1,1,2,1,1,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121121112
theorem R12112112 : good true 2 (pref true [2,1,1,2,1,1,2]) 2 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,2,1,1,2]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121121120
  · change good true 2 (step (pref true [2,1,1,2,1,1,2]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121121121
  · exact (hk (by decide)).elim
theorem R12112120 : good true 2 (pref true [2,1,1,2,1,2,0]) 0 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,2,1,2,0]) 0) 0 8 = true
    rw [← pref_snoc]
    exact R121121200
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,2,1,2,0]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121121202
theorem R12112121 : good true 2 (pref true [2,1,1,2,1,2,1]) 1 9 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,2,1,2,1]) 1) 1 8 = true
    rw [← pref_snoc]
    exact R121121211
  · change good true 2 (step (pref true [2,1,1,2,1,2,1]) 2) 2 8 = true
    rw [← pref_snoc]
    exact R121121212
theorem R1211211 : good true 2 (pref true [2,1,1,2,1,1]) 1 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,2,1,1]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12112111
  · change good true 2 (step (pref true [2,1,1,2,1,1]) 2) 2 9 = true
    rw [← pref_snoc]
    exact R12112112
theorem R1211212 : good true 2 (pref true [2,1,1,2,1,2]) 2 10 = true := by
  apply join
  intro k hk
  fin_cases k
  · change good true 2 (step (pref true [2,1,1,2,1,2]) 0) 0 9 = true
    rw [← pref_snoc]
    exact R12112120
  · change good true 2 (step (pref true [2,1,1,2,1,2]) 1) 1 9 = true
    rw [← pref_snoc]
    exact R12112121
  · exact (hk (by decide)).elim
theorem R121121 : good true 2 (pref true [2,1,1,2,1]) 1 11 = true := by
  apply join
  intro k hk
  fin_cases k
  · exact (hk (by decide)).elim
  · change good true 2 (step (pref true [2,1,1,2,1]) 1) 1 10 = true
    rw [← pref_snoc]
    exact R1211211
  · change good true 2 (step (pref true [2,1,1,2,1]) 2) 2 10 = true
    rw [← pref_snoc]
    exact R1211212
end Ribbon5Owner
