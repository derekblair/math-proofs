import HaarClass7ParallelPairs
import HaarP3Class4Order

namespace HaarClass7ParallelCycle
open HaarClass7Parallel HaarUniversal36 HaarClass4Table HaarClass4Normal
open HaarP3Class4Collect HaarClass4Generate HaarClass4Ports HaarP3Class4Order
open HaarReducedWalkCycle HaarAllNoncommuting HaarHalfCollision
variable {G H : Type*} [Group G] [Group H]

theorem window (t : Fin 3) (i : ℕ) (l : lo t ≤ i) (u : i < hi t) :
    label (W t) i = label (W t) (i+32) := by
  have h : ∀ (t : Fin 3) (i : Fin 64), lo t≤ i.val → i.val<hi t →
    label (W t) i.val = label (W t) (i.val+32) := by decide
  have n : ∀ z : Fin 3, hi z ≤ 64 := by decide
  exact h t ⟨i,by have n' := n t; omega⟩ l u

theorem window_step (x y : G) (t : Fin 3) (i : ℕ) (l : lo t≤ i) (u : i<hi t) :
    (path x y (W t) i=path x y (W t) (i+32)) ↔
      (path x y (W t) (i+1)=path x y (W t) ((i+1)+32)) := by
  have e : signPort x y i (label (W t) i) = signPort x y (i+32) (label (W t) (i+32)) := by
    rw [←window t i l u]
    simp only [signPort]
    have p : i%2=(i+32)%2 := by omega
    rw [←p]
  rw [show i+1+32=i+32+1 by omega]
  change (path x y (W t) i=path x y (W t) (i+32)) ↔
    (path x y (W t) i * signPort x y i (label (W t) i) =
    path x y (W t) (i+32) * signPort x y (i+32) (label (W t) (i+32)))
  rw [e]
  exact ⟨fun h => congrArg (· * _) h, mul_right_cancel⟩

theorem window_all (x y : G) (t : Fin 3) {i j : ℕ}
    (li : lo t ≤ i) (ij : i ≤ j) (jh : j ≤ hi t) :
    (path x y (W t) i = path x y (W t) (i+32)) ↔
    (path x y (W t) j = path x y (W t) (j+32)) := by
  induction j with
  | zero => obtain rfl : i=0 := by omega
            rfl
  | succ j ih =>
    by_cases q : i=j+1
    · subst i
      rfl
    · exact (ih (by omega) (by omega)).trans
        (window_step x y t j (by omega) (by omega))

theorem neq_window (x y : G) (t : Fin 3) {i : ℕ} (li : lo t ≤ i) (ih : i ≤ hi t)
    (ne : path x y (W t) (midpt t) ≠ path x y (W t) (midpt t+32)) :
    path x y (W t) i ≠ path x y (W t) (i+32) := by
  intro e
  have qb : ∀ z : Fin 3, lo z ≤ midpt z ∧ midpt z ≤ hi z := by decide
  have q := qb t
  by_cases k : i ≤ midpt t
  · exact ne ((window_all x y t li k q.2).mp e)
  · exact ne ((window_all x y t q.1 (by omega) ih).mpr e)

theorem closes (nil : L G 7=⊥) (x y : G) (t : Fin 3) : prodFrom x y 0 (W t)=1 := by
  fin_cases t
  · exact close1 nil x y
  · exact close2 nil x y
  · exact close3 nil x y

theorem window_of_factors (x y : G) (t : Fin 3)
    (different : prodFrom x y 0 (A t) ≠ prodFrom x y 0 (B t)) :
    path x y (W t) (midpt t) ≠ path x y (W t) (midpt t+32) := by
  intro e
  have L : path x y (W t) (midpt t)=prodFrom x y 0 (A t) := by
    fin_cases t
    · change path x y W1 16 = prodFrom x y 0 A1
      norm_num [W1,A1,path,label,prodFrom,signPort,port] <;> group
    · change path x y W2 14 = prodFrom x y 0 A2
      norm_num [W2,A2,path,label,prodFrom,signPort,port] <;> group
    · change path x y W3 12 = prodFrom x y 0 A3
      norm_num [W3,A3,path,label,prodFrom,signPort,port] <;> group
  have R : path x y (W t) (midpt t + 32) =
      prodFrom x y 0 (A t)*prodFrom x y 0 (B t)*(prodFrom x y 0 (A t))⁻¹ := by
    fin_cases t
    · change path x y W1 48 = _
      norm_num [A,B,W1,A1,B1,path,label,prodFrom,signPort,port,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> group
    · change path x y W2 46 = _
      norm_num [A,B,W2,A2,B2,path,label,prodFrom,signPort,port,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> group
    · change path x y W3 44 = _
      norm_num [A,B,W3,A3,B3,path,label,prodFrom,signPort,port,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> group

  rw [L,R] at e
  apply different
  have h := congrArg (fun w => w*(prodFrom x y 0 (A t))) e
  change prodFrom x y 0 (A t)*prodFrom x y 0 (A t) = _ at h
  simp only [mul_assoc,inv_mul_cancel,mul_one] at h
  exact mul_left_cancel h

end HaarClass7ParallelCycle
#print axioms HaarClass7ParallelCycle.window_of_factors
