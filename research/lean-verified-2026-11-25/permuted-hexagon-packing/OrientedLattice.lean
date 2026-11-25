import Gauge
import ApproxRows

namespace PermHex
open PermCircles (rotate)

structure Mat where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def act (M : Mat) (x y : ℝ) : Point :=
  (M.a*x+M.b*y,M.c*x+M.d*y)
def detR (M : Mat) : ℝ := M.a*M.d-M.b*M.c

noncomputable def areaUnit : ℝ := 3*root3/2

noncomputable def ideal (c s : ℝ) : Mat :=
  ⟨c*root3,c*root3/2-s*3/2,s*root3,s*root3/2+c*3/2⟩

lemma ideal_det {c s : ℝ} (h : c^2+s^2=1) : detR (ideal c s)=areaUnit := by
  unfold detR ideal areaUnit
  dsimp
  linear_combination (3*root3/2)*h

lemma areaUnit_pos : 0<areaUnit := by unfold areaUnit; have := root3_pos; positivity

lemma ideal_act (c s a b : ℝ) :
    act (ideal c s) a b=rotate c (-s) (base a b) := by
  apply Prod.ext <;> simp only [act,ideal,base,rotate] <;> ring

lemma ideal_gauge {c s : ℝ} (h : c^2+s^2=1) (a b : ℝ) :
    gaugeR c s (act (ideal c s) a b)=gauge (base a b) := by
  rw [ideal_act,gaugeR]
  have h' : c^2+(-s)^2=1 := by simpa using h
  have he := PermCircles.rot_neg_inv h' (base a b)
  simpa [neg_neg] using congrArg gauge he

lemma rotate_add (c s : ℝ) (x y : Point) :
    rotate c s (x+y)=rotate c s x+rotate c s y := by
  apply Prod.ext <;> simp [rotate] <;> ring

lemma gaugeR_triangle (c s : ℝ) (x y : Point) :
    gaugeR c s (x+y)≤gaugeR c s x+gaugeR c s y := by
  unfold gaugeR
  rw [rotate_add]
  exact gauge_triangle _ _

lemma gaugeR_smul (c s r : ℝ) (z : Point) :
    gaugeR c s (r • z)=|r| * gaugeR c s z := by
  unfold gaugeR
  rw [PermCircles.rot_smul,gauge_smul]

def Close (r ε : ℝ) (M I : Mat) : Prop :=
    |M.a-r*I.a|≤ε*r ∧ |M.b-r*I.b|≤ε*r ∧ |M.c-r*I.c|≤ε*r ∧ |M.d-r*I.d|≤ε*r

lemma act_close {r ε : ℝ} {M I : Mat} (h : Close r ε M I) (x y : ℝ) :
    l1 ((r • act I x y)-act M x y)≤2*ε*r*(|x|+|y|) := by
  rcases h with ⟨ha,hb,hc,hd⟩
  have hx : ((r • act I x y)-act M x y).1 =
      -((M.a-r*I.a)*x+(M.b-r*I.b)*y) := by simp [act] <;> ring
  have hy : ((r • act I x y)-act M x y).2 =
      -((M.c-r*I.c)*x+(M.d-r*I.d)*y) := by simp [act] <;> ring
  unfold l1
  rw [hx,hy,abs_neg,abs_neg]
  have h1 := abs_add_le ((M.a-r*I.a)*x) ((M.b-r*I.b)*y)
  have h2 := abs_add_le ((M.c-r*I.c)*x) ((M.d-r*I.d)*y)
  rw [abs_mul,abs_mul] at h1 h2
  have ha' := mul_le_mul_of_nonneg_right ha (abs_nonneg x)
  have hb' := mul_le_mul_of_nonneg_right hb (abs_nonneg y)
  have hc' := mul_le_mul_of_nonneg_right hc (abs_nonneg x)
  have hd' := mul_le_mul_of_nonneg_right hd (abs_nonneg y)
  linarith

theorem close_basis_separation {c s r ε : ℝ} (hU : c^2+s^2=1)
    (hr : 0≤r) (hε : 0≤ε) (hε' : 12*ε≤1) {M : Mat} (h : Close r ε M (ideal c s))
    {x y : ℤ} (hne : x≠0 ∨ y≠0) :
    2*r*(1-12*ε)≤gaugeR c s (act M x y) := by
  let I := ideal c s
  let a := (x:ℝ)
  let b := (y:ℝ)
  let v := act M a b
  let w := r • act I a b
  have hC := act_close h a b
  have hB := gaugeR_l1 hU (w-v)
  have hFib : gaugeR c s (w-v)≤8*ε*r*(|a|+|b|) := by
    change l1 (w-v)≤_ at hC
    linarith
  have hc := gauge_base_coefficients a b
  have hCoeff := mul_le_mul_of_nonneg_left hc (show 0≤8*ε*r by positivity)
  have hdiff : gaugeR c s (w-v)≤12*ε*r*gauge (base a b) := by linarith
  have ht := gaugeR_triangle c s v (w-v)
  have hw : gaugeR c s w≤gaugeR c s v+gaugeR c s (w-v) := by simpa [add_sub_cancel] using ht
  have hi : gaugeR c s w=r*gauge (base a b) := by
    dsimp only [w,I]
    rw [gaugeR_smul,abs_of_nonneg hr,ideal_gauge hU]
  have hmin : 2≤gauge (base a b) := gauge_base_integer_min hne
  have hf := mul_le_mul_of_nonneg_right hmin (show 0≤r*(1-12*ε) by
    exact mul_nonneg hr (by linarith))
  linarith

#print axioms close_basis_separation
end PermHex
