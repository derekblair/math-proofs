import HaarMetaS013Voltage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.OrderOfElement

namespace HaarMetaS013Gauge
open HaarMetaS013Voltage
variable {A : Type*} [AddCommGroup A]

def potential (W : B → B → A) : B → A :=
  ![0,0 + W 0 11 - W 1 11,0 + W 0 11 - W 1 11 + W 1 12 - W 2 12,0 + W 0 13 - W 3 13,0 + W 0 11 - W 1 11 + W 1 14 - W 4 14,0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15,0 + W 0 13 - W 3 13 + W 3 16 - W 6 16,0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17 - W 7 17,0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18 - W 8 18,0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19 - W 9 19,0 + W 0 10,0 + W 0 11,0 + W 0 11 - W 1 11 + W 1 12,0 + W 0 13,0 + W 0 11 - W 1 11 + W 1 14,0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15,0 + W 0 13 - W 3 13 + W 3 16,0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17,0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18,0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19]
def weights (W : B → B → A) : Fin 7 → A :=
  ![W 2 13 + potential W 2 - potential W 13,W 3 14 + potential W 3 - potential W 14,W 4 15 + potential W 4 - potential W 15,W 5 16 + potential W 5 - potential W 16,W 6 17 + potential W 6 - potential W 17,W 7 18 + potential W 7 - potential W 18,W 8 19 + potential W 8 - potential W 19]

def map (W : B → B → A) : V →+ A where
  toFun q := ∑ k : Fin 7, q k • weights W k
  map_zero' := by simp
  map_add' q r := by simp [add_zsmul,Finset.sum_add_distrib]

def clean (W : B → B → A) (u v : B) : A := if u=v then 0 else W u v

theorem map_single (W : B → B → A) (i : Fin 7) (c : ℤ) :
    map W (fun j => if j=i then c else 0) = c • weights W i := by
  change (∑ j : Fin 7, (if j=i then c else 0) • weights W j) = _
  simp [ite_smul]

set_option maxHeartbeats 0 in
theorem map_gauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v)
    (u : B) (j : P) :
    map W (gauge u (next u j)) = clean W u (next u j) + potential W u - potential W (next u j) := by
  fin_cases u <;> fin_cases j
  · change map W (gauge 0 10) = clean W 0 10 + potential W 0 - potential W 10
    have e : gauge 0 10 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 0 10 + (0) - (0 + W 0 10)
    simp [clean] <;> abel
  · change map W (gauge 0 11) = clean W 0 11 + potential W 0 - potential W 11
    have e : gauge 0 11 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 0 11 + (0) - (0 + W 0 11)
    simp [clean] <;> abel
  · change map W (gauge 0 13) = clean W 0 13 + potential W 0 - potential W 13
    have e : gauge 0 13 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 0 13 + (0) - (0 + W 0 13)
    simp [clean] <;> abel
  · change map W (gauge 1 11) = clean W 1 11 + potential W 1 - potential W 11
    have e : gauge 1 11 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 1 11 + (0 + W 0 11 - W 1 11) - (0 + W 0 11)
    simp [clean] <;> abel
  · change map W (gauge 1 12) = clean W 1 12 + potential W 1 - potential W 12
    have e : gauge 1 12 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 1 12 + (0 + W 0 11 - W 1 11) - (0 + W 0 11 - W 1 11 + W 1 12)
    simp [clean] <;> abel
  · change map W (gauge 1 14) = clean W 1 14 + potential W 1 - potential W 14
    have e : gauge 1 14 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 1 14 + (0 + W 0 11 - W 1 11) - (0 + W 0 11 - W 1 11 + W 1 14)
    simp [clean] <;> abel
  · change map W (gauge 2 12) = clean W 2 12 + potential W 2 - potential W 12
    have e : gauge 2 12 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 2 12 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12) - (0 + W 0 11 - W 1 11 + W 1 12)
    simp [clean] <;> abel
  · change map W (gauge 2 13) = clean W 2 13 + potential W 2 - potential W 13
    have e : gauge 2 13 = (fun k : Fin 7 => if k=0 then (1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (1:ℤ) • (W 2 13 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12) - (0 + W 0 13)) = clean W 2 13 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12) - (0 + W 0 13)
    simp [clean] <;> abel
  · change map W (gauge 2 15) = clean W 2 15 + potential W 2 - potential W 15
    have e : gauge 2 15 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 2 15 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15)
    simp [clean] <;> abel
  · change map W (gauge 3 13) = clean W 3 13 + potential W 3 - potential W 13
    have e : gauge 3 13 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 3 13 + (0 + W 0 13 - W 3 13) - (0 + W 0 13)
    simp [clean] <;> abel
  · change map W (gauge 3 14) = clean W 3 14 + potential W 3 - potential W 14
    have e : gauge 3 14 = (fun k : Fin 7 => if k=1 then (1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (1:ℤ) • (W 3 14 + (0 + W 0 13 - W 3 13) - (0 + W 0 11 - W 1 11 + W 1 14)) = clean W 3 14 + (0 + W 0 13 - W 3 13) - (0 + W 0 11 - W 1 11 + W 1 14)
    simp [clean] <;> abel
  · change map W (gauge 3 16) = clean W 3 16 + potential W 3 - potential W 16
    have e : gauge 3 16 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 3 16 + (0 + W 0 13 - W 3 13) - (0 + W 0 13 - W 3 13 + W 3 16)
    simp [clean] <;> abel
  · change map W (gauge 4 14) = clean W 4 14 + potential W 4 - potential W 14
    have e : gauge 4 14 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 4 14 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14) - (0 + W 0 11 - W 1 11 + W 1 14)
    simp [clean] <;> abel
  · change map W (gauge 4 15) = clean W 4 15 + potential W 4 - potential W 15
    have e : gauge 4 15 = (fun k : Fin 7 => if k=2 then (1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (1:ℤ) • (W 4 15 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15)) = clean W 4 15 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15)
    simp [clean] <;> abel
  · change map W (gauge 4 17) = clean W 4 17 + potential W 4 - potential W 17
    have e : gauge 4 17 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 4 17 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14) - (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17)
    simp [clean] <;> abel
  · change map W (gauge 5 15) = clean W 5 15 + potential W 5 - potential W 15
    have e : gauge 5 15 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 5 15 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15)
    simp [clean] <;> abel
  · change map W (gauge 5 16) = clean W 5 16 + potential W 5 - potential W 16
    have e : gauge 5 16 = (fun k : Fin 7 => if k=3 then (1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (1:ℤ) • (W 5 16 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15) - (0 + W 0 13 - W 3 13 + W 3 16)) = clean W 5 16 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15) - (0 + W 0 13 - W 3 13 + W 3 16)
    simp [clean] <;> abel
  · change map W (gauge 5 18) = clean W 5 18 + potential W 5 - potential W 18
    have e : gauge 5 18 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 5 18 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18)
    simp [clean] <;> abel
  · change map W (gauge 6 16) = clean W 6 16 + potential W 6 - potential W 16
    have e : gauge 6 16 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 6 16 + (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16) - (0 + W 0 13 - W 3 13 + W 3 16)
    simp [clean] <;> abel
  · change map W (gauge 6 17) = clean W 6 17 + potential W 6 - potential W 17
    have e : gauge 6 17 = (fun k : Fin 7 => if k=4 then (1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (1:ℤ) • (W 6 17 + (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16) - (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17)) = clean W 6 17 + (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16) - (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17)
    simp [clean] <;> abel
  · change map W (gauge 6 19) = clean W 6 19 + potential W 6 - potential W 19
    have e : gauge 6 19 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 6 19 + (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16) - (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19)
    simp [clean] <;> abel
  · change map W (gauge 7 17) = clean W 7 17 + potential W 7 - potential W 17
    have e : gauge 7 17 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 7 17 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17 - W 7 17) - (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17)
    simp [clean] <;> abel
  · change map W (gauge 7 18) = clean W 7 18 + potential W 7 - potential W 18
    have e : gauge 7 18 = (fun k : Fin 7 => if k=5 then (1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (1:ℤ) • (W 7 18 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17 - W 7 17) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18)) = clean W 7 18 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17 - W 7 17) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18)
    simp [clean] <;> abel
  · change map W (gauge 7 7) = clean W 7 7 + potential W 7 - potential W 7
    have e : gauge 7 7 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 7 7 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17 - W 7 17) - (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17 - W 7 17)
    simp [clean] <;> abel
  · change map W (gauge 8 18) = clean W 8 18 + potential W 8 - potential W 18
    have e : gauge 8 18 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 8 18 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18 - W 8 18) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18)
    simp [clean] <;> abel
  · change map W (gauge 8 19) = clean W 8 19 + potential W 8 - potential W 19
    have e : gauge 8 19 = (fun k : Fin 7 => if k=6 then (1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (1:ℤ) • (W 8 19 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18 - W 8 18) - (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19)) = clean W 8 19 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18 - W 8 18) - (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19)
    simp [clean] <;> abel
  · change map W (gauge 8 8) = clean W 8 8 + potential W 8 - potential W 8
    have e : gauge 8 8 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 8 8 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18 - W 8 18) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18 - W 8 18)
    simp [clean] <;> abel
  · change map W (gauge 9 19) = clean W 9 19 + potential W 9 - potential W 19
    have e : gauge 9 19 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 9 19 + (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19 - W 9 19) - (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19)
    simp [clean] <;> abel
  · change map W (gauge 9 9) = clean W 9 9 + potential W 9 - potential W 9
    have e : gauge 9 9 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 9 9 + (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19 - W 9 19) - (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19 - W 9 19)
    simp [clean] <;> abel
  · change map W (gauge 9 9) = clean W 9 9 + potential W 9 - potential W 9
    have e : gauge 9 9 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 9 9 + (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19 - W 9 19) - (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19 - W 9 19)
    simp [clean] <;> abel
  · change map W (gauge 10 0) = clean W 10 0 + potential W 10 - potential W 0
    have e : gauge 10 0 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 10 0 + (0 + W 0 10) - (0)
    simp [clean,anti 0 10] <;> abel
  · change map W (gauge 10 10) = clean W 10 10 + potential W 10 - potential W 10
    have e : gauge 10 10 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 10 10 + (0 + W 0 10) - (0 + W 0 10)
    simp [clean] <;> abel
  · change map W (gauge 10 10) = clean W 10 10 + potential W 10 - potential W 10
    have e : gauge 10 10 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 10 10 + (0 + W 0 10) - (0 + W 0 10)
    simp [clean] <;> abel
  · change map W (gauge 11 1) = clean W 11 1 + potential W 11 - potential W 1
    have e : gauge 11 1 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 11 1 + (0 + W 0 11) - (0 + W 0 11 - W 1 11)
    simp [clean,anti 1 11] <;> abel
  · change map W (gauge 11 0) = clean W 11 0 + potential W 11 - potential W 0
    have e : gauge 11 0 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 11 0 + (0 + W 0 11) - (0)
    simp [clean,anti 0 11] <;> abel
  · change map W (gauge 11 11) = clean W 11 11 + potential W 11 - potential W 11
    have e : gauge 11 11 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 11 11 + (0 + W 0 11) - (0 + W 0 11)
    simp [clean] <;> abel
  · change map W (gauge 12 2) = clean W 12 2 + potential W 12 - potential W 2
    have e : gauge 12 2 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 12 2 + (0 + W 0 11 - W 1 11 + W 1 12) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12)
    simp [clean,anti 2 12] <;> abel
  · change map W (gauge 12 1) = clean W 12 1 + potential W 12 - potential W 1
    have e : gauge 12 1 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 12 1 + (0 + W 0 11 - W 1 11 + W 1 12) - (0 + W 0 11 - W 1 11)
    simp [clean,anti 1 12] <;> abel
  · change map W (gauge 12 12) = clean W 12 12 + potential W 12 - potential W 12
    have e : gauge 12 12 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 12 12 + (0 + W 0 11 - W 1 11 + W 1 12) - (0 + W 0 11 - W 1 11 + W 1 12)
    simp [clean] <;> abel
  · change map W (gauge 13 3) = clean W 13 3 + potential W 13 - potential W 3
    have e : gauge 13 3 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 13 3 + (0 + W 0 13) - (0 + W 0 13 - W 3 13)
    simp [clean,anti 3 13] <;> abel
  · change map W (gauge 13 2) = clean W 13 2 + potential W 13 - potential W 2
    have e : gauge 13 2 = (fun k : Fin 7 => if k=0 then (-1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (-1:ℤ) • (W 2 13 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12) - (0 + W 0 13)) = clean W 13 2 + (0 + W 0 13) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12)
    simp [clean,anti 2 13] <;> abel
  · change map W (gauge 13 0) = clean W 13 0 + potential W 13 - potential W 0
    have e : gauge 13 0 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 13 0 + (0 + W 0 13) - (0)
    simp [clean,anti 0 13] <;> abel
  · change map W (gauge 14 4) = clean W 14 4 + potential W 14 - potential W 4
    have e : gauge 14 4 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 14 4 + (0 + W 0 11 - W 1 11 + W 1 14) - (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14)
    simp [clean,anti 4 14] <;> abel
  · change map W (gauge 14 3) = clean W 14 3 + potential W 14 - potential W 3
    have e : gauge 14 3 = (fun k : Fin 7 => if k=1 then (-1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (-1:ℤ) • (W 3 14 + (0 + W 0 13 - W 3 13) - (0 + W 0 11 - W 1 11 + W 1 14)) = clean W 14 3 + (0 + W 0 11 - W 1 11 + W 1 14) - (0 + W 0 13 - W 3 13)
    simp [clean,anti 3 14] <;> abel
  · change map W (gauge 14 1) = clean W 14 1 + potential W 14 - potential W 1
    have e : gauge 14 1 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 14 1 + (0 + W 0 11 - W 1 11 + W 1 14) - (0 + W 0 11 - W 1 11)
    simp [clean,anti 1 14] <;> abel
  · change map W (gauge 15 5) = clean W 15 5 + potential W 15 - potential W 5
    have e : gauge 15 5 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 15 5 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15)
    simp [clean,anti 5 15] <;> abel
  · change map W (gauge 15 4) = clean W 15 4 + potential W 15 - potential W 4
    have e : gauge 15 4 = (fun k : Fin 7 => if k=2 then (-1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (-1:ℤ) • (W 4 15 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15)) = clean W 15 4 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15) - (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14)
    simp [clean,anti 4 15] <;> abel
  · change map W (gauge 15 2) = clean W 15 2 + potential W 15 - potential W 2
    have e : gauge 15 2 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 15 2 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12)
    simp [clean,anti 2 15] <;> abel
  · change map W (gauge 16 6) = clean W 16 6 + potential W 16 - potential W 6
    have e : gauge 16 6 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 16 6 + (0 + W 0 13 - W 3 13 + W 3 16) - (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16)
    simp [clean,anti 6 16] <;> abel
  · change map W (gauge 16 5) = clean W 16 5 + potential W 16 - potential W 5
    have e : gauge 16 5 = (fun k : Fin 7 => if k=3 then (-1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (-1:ℤ) • (W 5 16 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15) - (0 + W 0 13 - W 3 13 + W 3 16)) = clean W 16 5 + (0 + W 0 13 - W 3 13 + W 3 16) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15)
    simp [clean,anti 5 16] <;> abel
  · change map W (gauge 16 3) = clean W 16 3 + potential W 16 - potential W 3
    have e : gauge 16 3 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 16 3 + (0 + W 0 13 - W 3 13 + W 3 16) - (0 + W 0 13 - W 3 13)
    simp [clean,anti 3 16] <;> abel
  · change map W (gauge 17 7) = clean W 17 7 + potential W 17 - potential W 7
    have e : gauge 17 7 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 17 7 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17) - (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17 - W 7 17)
    simp [clean,anti 7 17] <;> abel
  · change map W (gauge 17 6) = clean W 17 6 + potential W 17 - potential W 6
    have e : gauge 17 6 = (fun k : Fin 7 => if k=4 then (-1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (-1:ℤ) • (W 6 17 + (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16) - (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17)) = clean W 17 6 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17) - (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16)
    simp [clean,anti 6 17] <;> abel
  · change map W (gauge 17 4) = clean W 17 4 + potential W 17 - potential W 4
    have e : gauge 17 4 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 17 4 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17) - (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14)
    simp [clean,anti 4 17] <;> abel
  · change map W (gauge 18 8) = clean W 18 8 + potential W 18 - potential W 8
    have e : gauge 18 8 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 18 8 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18 - W 8 18)
    simp [clean,anti 8 18] <;> abel
  · change map W (gauge 18 7) = clean W 18 7 + potential W 18 - potential W 7
    have e : gauge 18 7 = (fun k : Fin 7 => if k=5 then (-1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (-1:ℤ) • (W 7 18 + (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17 - W 7 17) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18)) = clean W 18 7 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18) - (0 + W 0 11 - W 1 11 + W 1 14 - W 4 14 + W 4 17 - W 7 17)
    simp [clean,anti 7 18] <;> abel
  · change map W (gauge 18 5) = clean W 18 5 + potential W 18 - potential W 5
    have e : gauge 18 5 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 18 5 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15)
    simp [clean,anti 5 18] <;> abel
  · change map W (gauge 19 9) = clean W 19 9 + potential W 19 - potential W 9
    have e : gauge 19 9 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 19 9 + (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19) - (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19 - W 9 19)
    simp [clean,anti 9 19] <;> abel
  · change map W (gauge 19 8) = clean W 19 8 + potential W 19 - potential W 8
    have e : gauge 19 8 = (fun k : Fin 7 => if k=6 then (-1:ℤ) else 0) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_single]
    change (-1:ℤ) • (W 8 19 + (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18 - W 8 18) - (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19)) = clean W 19 8 + (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19) - (0 + W 0 11 - W 1 11 + W 1 12 - W 2 12 + W 2 15 - W 5 15 + W 5 18 - W 8 18)
    simp [clean,anti 8 19] <;> abel
  · change map W (gauge 19 6) = clean W 19 6 + potential W 19 - potential W 6
    have e : gauge 19 6 = (0:V) := by funext k; fin_cases k <;> decide +kernel
    rw [e,map_zero]
    change (0:A) = clean W 19 6 + (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16 + W 6 19) - (0 + W 0 13 - W 3 13 + W 3 16 - W 6 16)
    simp [clean,anti 6 19] <;> abel

def adj (W : B → B → A) (s t : B × A) : Prop :=
  ∃ j, next s.1 j = t.1 ∧ s.2 + clean W s.1 t.1 = t.2

def HasCycle (W : B → B → A) (n : ℕ) : Prop :=
  ∃ v : Fin n → B × A, Function.Injective v ∧
    ∀ i, adj W (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem ungauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v) {n : Nat}
    (C : HaarMetaS013Voltage.HasCycle (map W) n) : HasCycle W n := by
  obtain ⟨v,inj,cv⟩ := C
  let f (s : B × A) : B × A := (s.1,s.2 + potential W s.1)
  have fi : Function.Injective f := by
    rintro ⟨u,a⟩ ⟨v,b⟩ e
    have g : u=v := congrArg (fun k : B × A => k.1) e
    subst v
    have h : a + potential W u = b + potential W u := congrArg (fun k : B × A => k.2) e
    exact congrArg (Prod.mk u) (add_right_cancel h)
  refine ⟨f ∘ v,fi.comp inj,?_⟩
  intro i
  let j : Fin n := ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
  obtain ⟨k,hk,e⟩ := cv i
  have m := map_gauge W anti (v i).1 k
  rw [hk] at m
  change (v i).2 + map W (gauge (v i).1 (v j).1) = (v j).2 at e
  rw [m] at e
  refine ⟨k,hk,?_⟩
  change (v i).2+potential W (v i).1+clean W (v i).1 (v j).1 = (v j).2+potential W (v j).1
  rw [← e]
  abel

end HaarMetaS013Gauge
