import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace HaarMetaS025Voltage
abbrev V := Fin 7 → ℤ
abbrev B := Fin 26
abbrev P := Fin 3
abbrev State := B × V

def nextTable : B → P → B := ![![13,15,18],![14,16,19],![15,17,20],![16,18,21],![17,19,22],![18,20,23],![19,21,24],![20,22,25],![21,23,8],![22,24,9],![23,25,10],![24,11,11],![25,12,12],![0,13,13],![1,14,14],![2,0,15],![3,1,16],![4,2,17],![5,3,0],![6,4,1],![7,5,2],![8,6,3],![9,7,4],![10,8,5],![11,9,6],![12,10,7]]
def next (u : B) (j : P) : B := nextTable u j

def gauge (u v : B) : V :=
  let a := min u.val v.val
  let b := max u.val v.val
  let t : ℤ := if u.val < 13 then 1 else -1
  fun i => if (a,b) = ((![(4,19),(5,20),(6,21),(7,22),(8,23),(9,24),(10,25)] : Fin 7 → ℕ × ℕ) i) then t else 0

def step (s : State) (j : P) : State :=
  let v := next s.1 j
  (v,s.2+gauge s.1 v)

def start : State := (5,0)
def rows (s : State) : List P → List State
  | [] => []
  | j::w => s :: rows (step s j) w

def finish (s : State) : List P → State
  | [] => s
  | j::w => finish (step s j) w

@[simp] theorem rows_length (s : State) (w : List P) : (rows s w).length=w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons _ _ ih => simp [rows,ih]

variable {A : Type*} [AddCommGroup A]
def lift (φ : V →+ A) (s : State) : B × A := (s.1,φ s.2)

def adj (φ : V →+ A) (s t : B × A) : Prop :=
  ∃ j, next s.1 j = t.1 ∧ s.2 + φ (gauge s.1 t.1) = t.2

theorem step_adj (φ : V →+ A) (s : State) (j : P) :
    adj φ (lift φ s) (lift φ (step s j)) := by
  exact ⟨j,rfl,(map_add φ _ _).symm⟩

def HasCycle (φ : V →+ A) (n : ℕ) : Prop :=
  ∃ v : Fin n → B × A, Function.Injective v ∧
    ∀ i, adj φ (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem rows_adj (φ : V →+ A) (s : State) (w : List P)
    (i : ℕ) (hi : i < (rows s w).length) (hj : i+1 < (rows s w).length) :
    adj φ (lift φ ((rows s w)[i])) (lift φ ((rows s w)[i+1])) := by
  induction w generalizing s i with
  | nil => simp at hi
  | cons j w ih =>
    cases i with
    | zero =>
      cases w with
      | nil => simp at hj
      | cons k W => exact step_adj φ s j
    | succ i => exact ih (step s j) i (by simpa [rows] using hi) (by simpa [rows] using hj)

theorem rows_final (φ : V →+ A) (s : State) (w : List P)
    (i : ℕ) (hi : i < (rows s w).length) (h : i+1 = (rows s w).length) :
    adj φ (lift φ ((rows s w)[i])) (lift φ (finish s w)) := by
  induction w generalizing s i with
  | nil => simp at hi
  | cons j w ih =>
    cases i with
    | zero =>
      cases w with
      | nil => exact step_adj φ s j
      | cons k W => simp at h
    | succ i => exact ih (step s j) i (by simpa [rows] using hi) (by simpa [rows] using h)

theorem from_rows (φ : V →+ A) (w : List P) (nonempty : 0<w.length)
    (cl : lift φ (finish start w) = lift φ start)
    (sep : ∀ i j : Fin w.length, i.val < j.val →
      lift φ ((rows start w)[i.val]'(by simpa using i.isLt)) ≠
        lift φ ((rows start w)[j.val]'(by simpa using j.isLt))) :
    HasCycle φ w.length := by
  let v (i : Fin w.length) := lift φ ((rows start w)[i.val]'(by simpa using i.isLt))
  refine ⟨v,?_,?_⟩
  · intro i j eq
    rcases lt_trichotomy i.val j.val with h|h|h
    · exact False.elim (sep i j h eq)
    · exact Fin.ext h
    · exact False.elim (sep j i h eq.symm)
  · intro i
    by_cases h : i.val+1 < w.length
    · have H := rows_adj φ start w i.val (by simpa using i.isLt) (by simpa using h)
      simpa [v,Nat.mod_eq_of_lt h] using H
    · have h' : i.val+1 = w.length := by omega
      have H := rows_final φ start w i.val (by simpa using i.isLt) (by simpa using h')
      rw [cl] at H
      cases w with
      | nil => simp at nonempty
      | cons a w =>
        have z : (i.val+1)%(w.length+1)=0 := by rw [h',List.length_cons,Nat.mod_self]
        simpa [v,z,rows] using H

end HaarMetaS025Voltage
