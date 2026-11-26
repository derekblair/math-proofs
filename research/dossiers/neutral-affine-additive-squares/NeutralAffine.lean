import Mathlib.Tactic

namespace NeutralAffine

theorem phase_step (s q z c : ℤ) (hs : s*s=1) :
    (q*s)*(s*z+c) = q*z + (q*s)*c := by
  calc
    (q*s)*(s*z+c) = q*(s*s)*z + (q*s)*c := by ring
    _ = _ := by rw [hs,mul_one]

theorem phase_zero (q z : ℤ) (hq : q*q=1) : q*z=0 ↔ z=0 := by
  constructor
  · intro h
    have he : q*(q*z)=q*0 := congrArg (q*·) h
    rw [← mul_assoc,hq,one_mul,mul_zero] at he
    exact he
  · rintro rfl; simp

theorem expanding_bound (a x c B C : ℝ)
    (ha : 1 < |a|) (hc : |c|≤C) (hB : C≤(|a|-1)*B) (h : |a*x+c|≤B) :
    |x|≤B := by
  have id : a*x=(a*x+c)+(-c) := by ring
  have e : |a*x| ≤ B+C := by
    calc
      |a*x| = |(a*x+c)+(-c)| := congrArg abs id
      _ ≤ |a*x+c|+|-c| := abs_add_le _ _
      _ ≤ B+C := by rw [abs_neg]; exact add_le_add h hc
  rw [abs_mul] at e
  have bp : B+C≤|a| *B := by linarith
  exact le_of_mul_le_mul_left (e.trans bp) (by linarith)

theorem contracting_bound (a x c B C : ℝ)
    (ha : |a|<1) (hc : |c|≤C) (hB : C≤(1-|a|)*B) (h : |x|≤B) :
    |a*x+c|≤B := by
  calc
    |a*x+c| ≤ |a*x| + |c| := abs_add_le _ _
    _ ≤ |a| *B+C := by rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_left h (abs_nonneg _)) hc
    _ ≤ B := by linarith

theorem projections_zero (a b c d x y : ℤ)
    (hi : a*d-b*c ≠ 0) (hx : a*x+b*y=0) (hy : c*x+d*y=0) :
    x=0 ∧ y=0 := by
  constructor
  · have h : (a*d-b*c)*x=0 := by linear_combination d*hx-b*hy
    exact (mul_eq_zero.mp h).resolve_left hi
  · have h : (a*d-b*c)*y=0 := by linear_combination a*hy-c*hx
    exact (mul_eq_zero.mp h).resolve_left hi

inductive Balanced : List ℤ → Prop
  | nil : Balanced []
  | append {a b} : Balanced a → Balanced b → Balanced (a++b)
  | pos {a} : Balanced a → Balanced ([1]++a++[-1])
  | neg {a} : Balanced a → Balanced ([-1]++a++[1])

theorem balanced_sound {a : List ℤ} (h : Balanced a) : a.sum=0 := by
  induction h with
  | nil => rfl
  | append h₁ h₂ a b => simp [a,b]
  | pos h₁ a => simp [a]
  | neg h₁ a => simp [a]

theorem rankOne_length_suffices (a b c d x y : ℤ)
    (singular : a*d-b*c=0) (length_nonzero : a ≠ 0 ∨ b ≠ 0)
    (len : a*x+b*y=0) :
    c*x+d*y=0 := by
  rcases length_nonzero with ha | hb
  · have h : a*(c*x+d*y)=0 := by linear_combination c*len + y*singular
    exact (mul_eq_zero.mp h).resolve_left ha
  · have h : b*(c*x+d*y)=0 := by linear_combination d*len - x*singular
    exact (mul_eq_zero.mp h).resolve_left hb

theorem separated_children (B I x y L : ℕ) (h : B+L≤I) (xbound : x<L) :
    B+x<I+y := by omega

theorem jordan_next (u v w r : ℤ) (diff : v=u+r) (rec : w+u=2*v) :
    w=v+r := by omega

theorem jordan_suffix_zero (A : List ℕ) (rate : ℕ) (preserved : (rate::A).sum=rate) :
    ∀ x ∈ A, x=0 := by
  have hsum : A.sum=0 := by simp at preserved; omega
  intro x hx
  have hh := List.le_sum_of_mem hx
  omega

end NeutralAffine

#print axioms NeutralAffine.phase_step
#print axioms NeutralAffine.phase_zero
#print axioms NeutralAffine.expanding_bound
#print axioms NeutralAffine.contracting_bound
#print axioms NeutralAffine.projections_zero
#print axioms NeutralAffine.balanced_sound

#print axioms NeutralAffine.rankOne_length_suffices
#print axioms NeutralAffine.separated_children
#print axioms NeutralAffine.jordan_next
#print axioms NeutralAffine.jordan_suffix_zero
