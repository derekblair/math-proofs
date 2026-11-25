import Rotation
import Mathlib.Tactic

namespace PermHex

abbrev Point := ℝ × ℝ
noncomputable def root3 : ℝ := Real.sqrt 3

lemma root3_sq : root3^2=3 := Real.sq_sqrt (by norm_num)
lemma root3_pos : 0<root3 := Real.sqrt_pos.2 (by norm_num)
lemma one_le_root3 : 1≤root3 := by
  have hp := root3_pos
  have h2 := root3_sq
  by_contra! h
  nlinarith [mul_nonneg (show 0≤1-root3 by linarith) (show 0≤1+root3 by linarith)]
lemma root3_le_two : root3≤2 := by
  have hp := root3_pos
  have h2 := root3_sq
  by_contra! h
  nlinarith [mul_nonneg (show 0≤root3-2 by linarith) (show 0≤root3+2 by linarith)]

noncomputable def gauge (z : Point) : ℝ :=
  max (2*|z.1|/root3) (|z.1|/root3+|z.2|)

lemma gauge_nonneg (z : Point) : 0≤gauge z := by
  have hp := root3_pos
  exact le_trans (by positivity) (le_max_left _ _)

lemma gauge_neg (z : Point) : gauge (-z)=gauge z := by
  simp [gauge]

lemma gauge_smul (r : ℝ) (z : Point) : gauge (r • z) = |r| *gauge z := by
  have hfac (v : ℝ) : (2*(|r| *v)/root3) = |r| *(2*v/root3) := by ring
  have hfac' (v w : ℝ) : |r| *v/root3+|r| *w = |r| *(v/root3+w) := by ring
  simp only [gauge,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,abs_mul,hfac,hfac']
  exact (mul_max_of_nonneg _ _ (abs_nonneg r)).symm

lemma gauge_triangle (z w : Point) : gauge (z+w) ≤ gauge z + gauge w := by
  have hP := root3_pos
  have hx := abs_add_le z.1 w.1
  have hy := abs_add_le z.2 w.2
  have hx₁ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by norm_num : (0:ℝ)≤2)) hP.le
  have hx₂ := div_le_div_of_nonneg_right hx hP.le
  have hz₁ : 2*|z.1|/root3≤gauge z := le_max_left _ _
  have hw₁ : 2*|w.1|/root3≤gauge w := le_max_left _ _
  have hz₂ : |z.1|/root3+|z.2|≤gauge z := le_max_right _ _
  have hw₂ : |w.1|/root3+|w.2|≤gauge w := le_max_right _ _
  apply max_le
  · change 2*|z.1+w.1|/root3≤gauge z+gauge w
    rw [mul_add,add_div] at hx₁
    linarith
  · change |z.1+w.1|/root3+|z.2+w.2|≤gauge z+gauge w
    rw [add_div] at hx₂
    linarith

def l1 (z : Point) : ℝ := |z.1|+|z.2|

lemma gauge_l1 (z : Point) : gauge z ≤ 2*l1 z := by
  have hp := root3_pos
  have h1 := one_le_root3
  have hcoef : |z.1|/root3≤|z.1| := by
    apply (div_le_iff₀ hp).2
    have hn := mul_nonneg (abs_nonneg z.1) (show 0≤root3-1 by linarith)
    nlinarith
  apply max_le
  · have he : 2*|z.1|/root3=2*(|z.1|/root3) := by ring
    rw [he]
    unfold l1
    linarith [abs_nonneg z.2]
  · unfold l1
    linarith [abs_nonneg z.1,abs_nonneg z.2]

lemma unit_cos_sin_bounds {c s : ℝ} (h : c^2+s^2=1) : |c|≤1 ∧ |s|≤1 := by
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg s]
  · apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg c]

open PermCircles (rotate)
lemma rotate_l1 {c s : ℝ} (h : c^2+s^2=1) (z : Point) : l1 (rotate c s z)≤2*l1 z := by
  obtain ⟨hc,hs⟩ := unit_cos_sin_bounds h
  have hx := abs_add_le (c*z.1) (s*z.2)
  have hy := abs_add_le (c*z.2) (-s*z.1)
  have h1 := mul_le_mul_of_nonneg_right hc (abs_nonneg z.1)
  have h2 := mul_le_mul_of_nonneg_right hs (abs_nonneg z.1)
  have h3 := mul_le_mul_of_nonneg_right hc (abs_nonneg z.2)
  have h4 := mul_le_mul_of_nonneg_right hs (abs_nonneg z.2)
  change |c*z.1+s*z.2|+|c*z.2-s*z.1|≤2*(|z.1|+|z.2|)
  simp only [abs_mul,abs_neg,neg_mul,←sub_eq_add_neg] at hx hy
  linarith

noncomputable def gaugeR (c s : ℝ) (z : Point) : ℝ := gauge (rotate c s z)

lemma gaugeR_l1 {c s : ℝ} (h : c^2+s^2=1) (z : Point) :
    gaugeR c s z≤4*l1 z := by
  have h1 := rotate_l1 h z
  have h2 := gauge_l1 (rotate c s z)
  unfold gaugeR
  linarith

noncomputable def base (a b : ℝ) : Point := (root3*(a+b/2),(3:ℝ)/2*b)

lemma gauge_base (a b : ℝ) :
    gauge (base a b)=max (2*|a+b/2|) (|a+b/2|+3/2*|b|) := by
  have hp := root3_pos
  simp only [gauge,base,abs_mul,abs_of_pos hp, abs_of_nonneg (by norm_num : (0:ℝ)≤3/2)]
  have he : root3*|a+b/2|/root3=|a+b/2| := mul_div_cancel_left₀ _ hp.ne'
  rw [show 2*(root3*|a+b/2|)/root3=2*(root3*|a+b/2|/root3) by ring,he]

lemma gauge_base_coefficients (a b : ℝ) : |a|+|b| ≤ (3:ℝ)/2*gauge (base a b) := by
  rw [gauge_base]
  let q : ℝ := max (2*|a+b/2|) (|a+b/2|+3/2*|b|)
  have h1 : 2*|a+b/2|≤q := le_max_left _ _
  have h2 : |a+b/2|+3/2*|b|≤q := le_max_right _ _
  have h3 : |a|≤|a+b/2|+|b|/2 := by
    have hh := abs_add_le (a+b/2) (-b/2)
    rw [show a+b/2+ -b/2=a by ring,abs_div,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at hh
    exact hh
  change |a|+|b|≤(3:ℝ)/2*q
  linarith [abs_nonneg (a+b/2)]

lemma cast_abs_ge_one {a : ℤ} (ha : a≠0) : 1≤|(a:ℝ)| := by
  have hh : (1:ℤ)≤|a| := by
    rw [le_abs]
    omega
  exact_mod_cast hh

lemma gauge_base_integer_min {a b : ℤ} (hne : a≠0 ∨ b≠0) :
    2≤gauge (base a b) := by
  rw [gauge_base]
  by_cases hb : b=0
  · subst b
    simp only [Int.cast_zero,zero_div,add_zero]
    have h0 : a≠0 := hne.resolve_right (by simp)
    exact (show 2≤2*|(a:ℝ)| by linarith [cast_abs_ge_one h0]).trans (le_max_left _ _)
  have hb1 : 1≤|(b:ℝ)| := cast_abs_ge_one hb
  by_cases hc : 2≤|b|
  · have hbr : (2:ℝ)≤|(b:ℝ)| := by exact_mod_cast hc
    exact (show 2≤|(a:ℝ)+(b:ℝ)/2|+3/2*|(b:ℝ)| by linarith [abs_nonneg ((a:ℝ)+(b:ℝ)/2)]).trans (le_max_right _ _)
  have hbc : b=1 ∨ b= -1 := by
    have hd := abs_lt.mp (Int.lt_of_not_ge hc)
    omega
  have hn : 2*a+b≠0 := by rcases hbc with h|h <;> omega
  have hx : (1:ℝ)≤|2*(a:ℝ)+(b:ℝ)| := by exact_mod_cast cast_abs_ge_one hn
  have hxx : |2*(a:ℝ)+(b:ℝ)|=2*|(a:ℝ)+(b:ℝ)/2| := by
    rw [show 2*(a:ℝ)+(b:ℝ)=2*((a:ℝ)+(b:ℝ)/2) by ring,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  rw [hxx] at hx
  exact (show 2≤|(a:ℝ)+(b:ℝ)/2|+3/2*|(b:ℝ)| by linarith).trans (le_max_right _ _)

#print axioms gauge_base_integer_min
end PermHex
