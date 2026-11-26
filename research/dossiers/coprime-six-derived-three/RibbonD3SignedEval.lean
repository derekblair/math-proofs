import RibbonD3MateCheck
import RibbonD3GridBasic

namespace RibbonD3SignedEval
open RibbonD3MateData
variable {G : Type*} [Group G]

def eval (f : ℤ → G) : List ℤ → G
  | [] => 1
  | a::w => f a * eval f w

theorem eval_append (f : ℤ → G) (u v : List ℤ) :
    eval f (u++v) = eval f u * eval f v := by
  induction u with
  | nil => simp [eval]
  | cons a w ih => simp [eval,ih,mul_assoc]

def redStep (out : List Int) (a : Int) : List Int :=
  match out with
  | b::bs => if b == -a then bs else a::out
  | [] => [a]

theorem redStep_sound (f : ℤ → G) (hf : ∀ a, f (-a) = (f a)⁻¹)
    (out : List ℤ) (a : ℤ) :
    eval f (redStep out a).reverse = eval f out.reverse * f a := by
  cases out with
  | nil => simp [redStep,eval]
  | cons b bs =>
    by_cases E : b = -a
    · subst b
      simp [redStep,eval_append,eval,hf,mul_assoc]
    · simp [redStep,E,eval_append,eval,mul_assoc]

theorem fold_sound (f : ℤ → G) (hf : ∀ a, f (-a) = (f a)⁻¹)
    (u v : List ℤ) :
    eval f (v.foldl redStep u).reverse = eval f u.reverse * eval f v := by
  induction v generalizing u with
  | nil => simp [eval]
  | cons a v ih =>
    simp [List.foldl_cons,ih,redStep_sound f hf,eval,mul_assoc]

theorem freeReduce_sound (f : ℤ → G) (hf : ∀ a, f (-a) = (f a)⁻¹)
    (w : List ℤ) : eval f (freeReduce w) = eval f w := by
  change eval f (w.foldl redStep []).reverse = _
  simpa [eval] using fold_sound f hf [] w

theorem eval_inverse (f : ℤ → G) (hf : ∀ a, f (-a) = (f a)⁻¹)
    (w : List ℤ) : eval f (inverse w) = (eval f w)⁻¹ := by
  induction w with
  | nil => simp [inverse,eval]
  | cons a w ih =>
    change eval f ((a::w).reverse.map Neg.neg) = _
    simp [List.reverse_cons,List.map_append,eval_append,show w.reverse.map Neg.neg = inverse w from rfl,
      ih,eval,hf,mul_inv_rev]

def letter (x y : G) (a : ℤ) : G :=
  if a = 0 then 1 else if a.natAbs == 1 then x^a
  else if a > 0 then y else y⁻¹

theorem neg_letter (x y : G) (a : ℤ) : letter x y (-a) = (letter x y a)⁻¹ := by
  by_cases hz : a=0
  · simp [hz,letter]
  · have hz' : -a ≠ 0 := neg_ne_zero.mpr hz
    by_cases h : a.natAbs=1
    · simp [letter,hz,hz',h,zpow_neg]
    · rcases lt_or_gt_of_ne hz with hneg|hpos
      · have q : 0 < -a := by omega
        simp [letter,hz,hz',h,not_le_of_gt hneg,not_lt_of_ge (le_of_lt hneg)]
      · have q : ¬ 0 < -a := by omega
        simp [letter,hz,hz',h,not_lt_of_ge (le_of_lt hpos),hpos]

theorem free_sound (x y : G) {u v : List ℤ} (h : freeReduce u = freeReduce v) :
    eval (letter x y) u = eval (letter x y) v := by
  rw [←freeReduce_sound _ (neg_letter x y) u, ←freeReduce_sound _ (neg_letter x y) v,h]

#print axioms free_sound
end RibbonD3SignedEval
