import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Monotone.Basic

namespace DirectedBoxDSP

variable {I K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def interp (a b : I → K) (t : K) (j : I) : K :=
  a j + t * (b j - a j)

theorem interp_own_diff (a b : I → K) (t : K) (i j : I) :
    interp a b t i - interp a b t j =
      (a i-a j) + t * ((b i-b j)-(a i-a j)) := by
  unfold interp
  ring

/-- Clipping to a smaller parameter interval preserves each commodity's
own-progress monotonicity; the original segment need not start in the box. -/
theorem interp_own_monotone (a b : I → K) (i j : I)
    (h : a i-a j ≤ b i-b j) :
    Monotone fun t => interp a b t i - interp a b t j := by
  intro x y hxy
  change interp a b x i - interp a b x j ≤ interp a b y i - interp a b y j
  rw [interp_own_diff, interp_own_diff]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hxy (sub_nonneg.mpr h))

/-- Two clipped points on distinct segments occur in original path order.
This gives the pairwise interval ordering needed for telescoping, even
when intervening portions of the path lie outside the box. -/
theorem separated_segments_progress (p : ℕ → I → K) (i j : I)
    (mono : Monotone fun n => p n i - p n j)
    {a b : ℕ} (hab : a < b) (s t : K) (hs : s ≤ 1) (ht : 0 ≤ t) :
    interp (p a) (p (a+1)) s i - interp (p a) (p (a+1)) s j ≤
      interp (p b) (p (b+1)) t i - interp (p b) (p (b+1)) t j := by
  have ha' := interp_own_monotone (p a) (p (a+1)) i j (mono (Nat.le_succ _)) hs
  have hb' := interp_own_monotone (p b) (p (b+1)) i j (mono (Nat.le_succ _)) ht
  unfold interp at ha' hb'
  have hmid := mono hab
  change p (a+1) i - p (a+1) j ≤ p b i - p b j at hmid
  unfold interp
  linarith

#print axioms interp_own_diff
#print axioms interp_own_monotone
#print axioms separated_segments_progress
end DirectedBoxDSP
