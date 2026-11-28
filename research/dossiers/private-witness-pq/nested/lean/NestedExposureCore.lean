import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace NestedExposure

structure Moments where
  e1 : Nat
  e2 : Nat
  e3 : Nat
  e4 : Nat
  deriving Repr, DecidableEq

def Moments.empty : Moments := ⟨0,0,0,0⟩

/-- Coefficients 1 through 4 of the product of (1 + wX). -/
def Moments.step (m : Moments) (x : Nat) : Moments :=
  ⟨m.e1+x,m.e2+x*m.e1,m.e3+x*m.e2,m.e4+x*m.e3⟩

def available (a : Nat) : Nat :=
  let u := 13-a
  u*(u-1)/2

theorem available_is_choose : ∀ e : Fin 14, available e.val = (13-e.val).choose 2 := by decide

def advance (m : Moments) (a : Nat) : Moments := m.step (available a)
def moments (l : List Nat) : Moments := l.foldl advance Moments.empty

theorem advance_comm (m : Moments) (a b : Nat) :
    advance (advance m a) b = advance (advance m b) a := by
  rcases m with ⟨w,x,y,z⟩
  unfold advance Moments.step
  congr 1 <;> ring

theorem moments_perm_aux (x y : List Nat) (p : x.Perm y) :
    ∀ start : Moments, x.foldl advance start=y.foldl advance start := by
  induction p with
  | nil => simp
  | cons v h ih =>
      intro s
      simpa only [List.foldl_cons] using ih (advance s v)
  | swap a b l =>
      intro s
      simp only [List.foldl_cons]
      rw [advance_comm]
  | trans _ _ ih jh =>
      intro s
      exact (ih s).trans (jh s)

theorem moments_perm (x y : List Nat) (p : x.Perm y) : moments x=moments y :=
  moments_perm_aux x y p _

/-- Compare the numerator at the exact mixture with a common denominator
4663897056 · 9816373; no floating operations occur. -/
def asymNum (s : Nat) (m : Moments) : Nat :=
  4738500*m.e4 + 5077873*9*(13-s)*m.e3

def asymAccept (s : Nat) (m : Moments) : Bool := decide (198656215348500 ≤ asymNum s m)

def symAccept (m : Moments) : Bool := decide (28140210 ≤ m.e4)

def scan (accept : Moments → Bool) : Nat → Nat → Nat → Moments → Bool
  | 0, rest, _, m => if rest=0 then accept m else true
  | k+1, rest, lower, m =>
    if lower*(k+1)>rest ∨ rest>13*(k+1) then true else
    (List.range 14).all (fun e =>
      if lower≤e ∧ e≤rest then scan accept k (rest-e) e (advance m e) else true)

private theorem sum_bounds (l : List Nat) (a : Nat)
    (lower : ∀ p∈l, a≤p) (upper : ∀ p∈l, p≤13) :
    a*l.length≤l.sum ∧ l.sum≤13*l.length := by
  induction l with
  | nil => simp
  | cons v r ih =>
      have b := ih (fun x hx => lower x (List.mem_cons_of_mem _ hx))
        (fun x hx => upper x (List.mem_cons_of_mem _ hx))
      have x := lower v (by simp)
      have y := upper v (by simp)
      simp only [List.sum_cons,List.length_cons,Nat.mul_succ]
      omega

/-- Every sorted legal list is covered by the recursively bounded verifier. -/
theorem scan_sound (accept : Moments → Bool) (l : List Nat) (lo : Nat) (m : Moments)
    (inc : l.Pairwise (· ≤ ·))
    (lower : ∀ x∈l, lo≤x) (upper : ∀ x∈l, x≤13)
    (h : scan accept l.length l.sum lo m = true) :
    accept (l.foldl advance m) = true := by
  induction l generalizing lo m with
  | nil => simpa [scan] using h
  | cons x l ih =>
      obtain ⟨xl,inc'⟩ := List.pairwise_cons.mp inc
      have bounds := sum_bounds (x::l) lo lower upper
      have n : ¬(lo*(x::l).length>(x::l).sum ∨ (x::l).sum>13*(x::l).length) := by omega
      have hn : ¬(lo*(l.length+1)>x+l.sum ∨ x+l.sum>13*(l.length+1)) := by simpa using n
      have q : (List.range 14).all (fun e =>
          if lo≤e ∧ e≤x+l.sum then scan accept l.length (x+l.sum-e) e (advance m e) else true) = true := by
        simpa only [List.length_cons,List.sum_cons,scan,if_neg hn] using h
      have rx : x∈List.range 14 := List.mem_range.mpr (by have := upper x (by simp); omega)
      have hx := List.all_eq_true.mp q x rx
      have a : lo≤x := lower x (by simp)
      have s : x≤x+l.sum := by omega
      have rr : x+l.sum-x=l.sum := by omega
      have both : lo≤x ∧ x≤x+l.sum := ⟨a,s⟩
      simp only [if_pos both,rr] at hx
      simpa only [List.foldl_cons] using ih x (advance m x) inc' xl
        (fun p hp => upper p (List.mem_cons_of_mem _ hp)) hx

#print axioms scan_sound
#print axioms moments_perm
end NestedExposure
