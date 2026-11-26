import RibbonAffineWords
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace RibbonAffine
open Ribbon5Bridge
variable {G K : Type*} [Group G] [Field K]
abbrev Mono := ℤ × ℤ × ℤ

structure Row where
  side : Bool
  i : ℤ
  j : ℤ
  tr : List Mono
  deriving DecidableEq, Inhabited

def zeroRow : Row := ⟨false,0,0,[]⟩

def march (r : Row) (p : P) : Row :=
  if p=2 then {r with side := !r.side}
  else if !r.side then
    if p=0 then {r with i:=r.i+1} else {r with i:=r.i-1}
  else if p=0 then {r with j:=r.j+1,tr:=(r.i,r.j,1)::r.tr}
  else {r with j:=r.j-1,tr:=(r.i,r.j-1,-1)::r.tr}

def mon (a b : Kˣ) (u : Mono) : K :=
  (u.2.2 : K) * (↑(a^u.1 * b^u.2.1) : K)

def pl (a b : Kˣ) (l : List Mono) : K := (l.map (mon a b)).sum

def eRow (a b : Kˣ) (r : Row) : Bool × Kˣ × K :=
  (r.side,a^r.i*b^r.j,pl a b r.tr)

def pp (a b : Kˣ) (s : Bool × Kˣ × K) (p : P) : Bool × Kˣ × K :=
  if p=2 then (!s.1,s.2)
  else if !s.1 then
    if p=0 then (s.1,s.2.1*a,s.2.2)
    else (s.1,s.2.1*a⁻¹,s.2.2)
  else if p=0 then (s.1,s.2.1*b,s.2.2+(s.2.1:K))
  else (s.1,s.2.1*b⁻¹,s.2.2-↑(s.2.1*b⁻¹))

theorem march_eval (a b : Kˣ) (r : Row) (p : P) :
    eRow a b (march r p) = pp a b (eRow a b r) p := by
  obtain ⟨s,i,j,v⟩ := r
  cases s <;> fin_cases p <;>
    simp [eRow,march,pp,pl,mon,zpow_add,zpow_sub,mul_assoc,mul_comm,mul_left_comm,
      sub_eq_add_neg,add_comm]

theorem tau_inv (μ : G →* Kˣ) (τ : G → K) (H : ∀ g h : G, τ (g*h)=τ g+(μ g:K)*τ h)
    (zero : τ 1=0) (x : G) : τ x⁻¹ = -(↑(μ x)⁻¹:K)*τ x := by
  have h := H x⁻¹ x
  rw [inv_mul_cancel,zero,map_inv] at h
  have r := eq_neg_of_add_eq_zero_left h.symm
  simpa only [neg_mul] using r

theorem action_eval (μ : G →* Kˣ) (τ : G → K) (H : ∀ g h : G, τ (g*h)=τ g+(μ g:K)*τ h)
    (zero : τ 1=0) (x y : G) (tx : τ x=0) (ty : τ y=1) (u : Bool×G) (p : P) :
    (fun d : Bool×G => (d.1,μ d.2,τ d.2)) (action x y u p) =
      pp (μ x) (μ y) (u.1, μ u.2, τ u.2) p := by
  have ti := tau_inv μ τ H zero
  rcases u with ⟨s,z⟩
  cases s <;> fin_cases p <;>
    simp [action,pp,H,tx,ty,ti,sub_eq_add_neg,Units.val_mul,mul_comm]

theorem run_eval (μ : G →* Kˣ) (τ : G → K) (H : ∀ g h : G, τ (g*h)=τ g+(μ g:K)*τ h)
    (zero : τ 1=0) (x y : G) (tx : τ x=0) (ty : τ y=1)
    (u : Bool×G) (r : Row) (e : (u.1,μ u.2,τ u.2)=eRow (μ x) (μ y) r) (w : List P) :
    (fun d : Bool×G => (d.1,μ d.2,τ d.2)) (run x y u w) =
      eRow (μ x) (μ y) (w.foldl march r) := by
  induction w generalizing u r with
  | nil => exact e
  | cons p w ih =>
    apply ih (action x y u p) (march r p)
    change (fun d : Bool × G => (d.1,μ d.2,τ d.2)) (action x y u p) = _
    rw [action_eval μ τ H zero x y tx ty u p,march_eval,e]

def position (k : Fin 8) (i : Nat) : Row :=
  ((word k).toList.take i).foldl march zeroRow

theorem position_sound (μ : G →* Kˣ) (τ : G → K) (H : ∀ g h : G, τ (g*h)=τ g+(μ g:K)*τ h)
    (zero : τ 1=0) (x y : G) (tx : τ x=0) (ty : τ y=1) (k : Fin 8) (i : Nat) :
    (fun d : Bool×G => (d.1, μ d.2,τ d.2)) (pathAt x y (word k) i) =
      eRow (μ x) (μ y) (position k i) :=
  run_eval μ τ H zero x y tx ty (start G) zeroRow (by simp [eRow,pl,zeroRow,start,zero]) _

end RibbonAffine
#print axioms RibbonAffine.position_sound
