import RobustFolkman
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

namespace RobustFolkman
open Finset

def isMono (a b c : Bool) : Bool := (a==b) && (b==c)

def mixed (a b c : Bool) : ℚ :=
  (if a=b then 0 else 1) + (if b=c then 0 else 1) + (if c=a then 0 else 1)

def monoUnit (a b c : Bool) : ℚ := if isMono a b c then 1 else 0

theorem local_identity (a b c : Bool) : mixed a b c + 2*monoUnit a b c=2 := by
  cases a <;> cases b <;> cases c <;> norm_num [mixed,monoUnit,isMono]

/-- A link-cut bound below two thirds yields a strict uniform
monochromatic margin, counting every mixed corner once. -/
theorem positive_mono_fraction {T : Type*} (s : Finset T) (a b c : T → Bool) (ρ : ℚ)
    (bound : (∑ t∈s, mixed (a t) (b t) (c t)) ≤
      (3*(1+ρ)/2)*(s.card : ℚ)) :
    ((1-3*ρ)/4)*(s.card : ℚ) ≤ ∑ t∈s, monoUnit (a t) (b t) (c t) := by
  have all := sum_congr (s₁ := s) (s₂ := s) rfl fun t _ =>
    local_identity (a t) (b t) (c t)
  rw [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul] at all
  linarith only [bound,all]

#print axioms positive_mono_fraction
end RobustFolkman
