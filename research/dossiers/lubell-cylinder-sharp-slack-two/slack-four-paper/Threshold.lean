import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
namespace Lubell4

def lo (t d : ℚ) : ℚ :=
  let u := t+d
  (u+4)*(u+3)/((t+1)*(t+2)) + (u+4)*(u+3)/(t+2) + (u+4)*(u+3)/2

def prod (t d : ℚ) : ℚ :=
  let u := t+d
  (u+3) + ((t+2)*(u+2)+1) + (t+3)

def gap (t d : ℚ) : ℚ := (t+3)*d*(d+5)+14-t^3-4*t^2-t

theorem score_gap (t d : ℚ) (ht : 1 ≤ t) :
    2*(t+1)*(lo t d - prod t d) = gap t d := by
  have h1 : t+1 ≠ 0 := by linarith
  have h2 : t+2 ≠ 0 := by linarith
  unfold lo prod gap
  dsimp
  field_simp
  <;> ring

theorem gap_mono (t a b : ℚ) (ht : 1 ≤ t) (ha : 0 ≤ a) (hab : a ≤ b) :
    gap t a ≤ gap t b := by
  have he : gap t b - gap t a = (t+3)*(b-a)*(a+b+5) := by unfold gap; ring
  have h : 0 ≤ (t+3)*(b-a)*(a+b+5) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  linarith

theorem upper_side (t d : ℚ) (ht : 1 ≤ t) (hd : t-1 ≤ d) :
    prod t d < lo t d := by
  have h0 : gap t (t-1) = 2*(t+1)^2 := by unfold gap; ring
  have h1 := gap_mono t (t-1) d ht (by linarith) hd
  have hp : 0 < 2*(t+1)^2 := by positivity
  have h2 : 0 < gap t d := by linarith
  rw [←score_gap t d ht] at h2
  by_contra! bad
  have h3 : 2*(t+1)*(lo t d-prod t d) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

theorem lower_side (t d : ℚ) (ht : 1 ≤ t) (h0 : 0 ≤ d) (hd : d ≤ t-2) :
    lo t d < prod t d := by
  have h1 : gap t (t-2) = -4*(t+1) := by unfold gap; ring
  have h2 := gap_mono t d (t-2) ht h0 hd
  have hn : gap t d < 0 := by linarith
  rw [←score_gap t d ht] at hn
  by_contra! bad
  have h3 : 0 ≤ 2*(t+1)*(lo t d - prod t d) := mul_nonneg (by positivity) (by linarith)
  linarith

/-- Integer transition for the two explicit scaled score formulas; not an
    upper bound on arbitrary families. -/
theorem integer_phase (t u : ℕ) (ht : 1 ≤ t) (htu : t ≤ u) :
    let d : ℚ := (u-t : ℕ)
    (2*t ≤ u+1 → prod t d < lo t d) ∧
      (u+1 < 2*t → lo t d < prod t d) := by
  dsimp
  have ht' : (1:ℚ) ≤ (t:ℚ) := by exact_mod_cast ht
  have he : ((↑(u-t) : ℚ)) = (u:ℚ) - (t:ℚ) := Nat.cast_sub htu
  rw [he]
  constructor
  · intro h
    have hp : (2:ℚ)*(t:ℚ) ≤ (u:ℚ)+1 := by exact_mod_cast h
    exact upper_side t ((u:ℚ)-t) ht' (by linarith)
  · intro h
    have hn : u+2 ≤ 2*t := by omega
    have hp : (u:ℚ)+2 ≤ (2:ℚ)*(t:ℚ) := by exact_mod_cast hn
    have hl : (t:ℚ) ≤ (u:ℚ) := by exact_mod_cast htu
    exact lower_side t ((u:ℚ)-t) ht' (by linarith) (by linarith)

#print axioms integer_phase
end Lubell4
