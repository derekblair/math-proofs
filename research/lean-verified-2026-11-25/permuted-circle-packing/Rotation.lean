import Clip
namespace PermCircles

def rotate (c s : ℝ) (z : Point) : Point := (c*z.1+s*z.2,c*z.2-s*z.1)

lemma rot_sq {c s : ℝ} (h : c^2+s^2=1) (z w : Point) :
    sqDist (rotate c s z) (rotate c s w) = sqDist z w := by
  unfold sqDist rotate
  simp only
  linear_combination ((z.1-w.1)^2+(z.2-w.2)^2)*h

lemma rot_zero (c s : ℝ) : rotate c s 0 = 0 := by ext <;> simp [rotate]

lemma rot_smul (c s t : ℝ) (z : Point) : rotate c s (t • z) = t • rotate c s z := by
  ext <;> simp [rotate] <;> ring

lemma rot_neg_inv {c s : ℝ} (h : c^2+s^2=1) (z : Point) :
    rotate c (-s) (rotate c s z) = z := by
  apply Prod.ext
  · simp only [rotate]
    linear_combination z.1*h
  · simp only [rotate]
    linear_combination z.2*h

lemma aligned {b : Point} {d : ℝ} (hd : 0 < d) (h : sqDist b 0=d^2) :
    rotate (b.1/d) (b.2/d) b = (d,0) := by
  have hh : b.1^2+b.2^2=d^2 := by simpa [sqDist] using h
  apply Prod.ext
  · simp only [rotate]
    field_simp [hd.ne']
    nlinarith
  · simp only [rotate]
    ring

lemma alignment_isometry {b : Point} {d : ℝ} (hd : 0 < d) (h : sqDist b 0=d^2) :
    (b.1/d)^2+(b.2/d)^2=1 := by
  have hh : b.1^2+b.2^2=d^2 := by simpa [sqDist] using h
  field_simp [hd.ne']
  nlinarith

lemma shadow_rotate {c s ρ : ℝ} (h : c^2+s^2=1) {b z : Point} :
    radialShadow ρ (rotate c s b) (rotate c s z) ↔ radialShadow ρ b z := by
  have hz : sqDist (rotate c s z) 0 = sqDist z 0 := by
    simpa only [rot_zero] using rot_sq h z 0
  simp only [radialShadow,hz,←rot_smul,rot_sq h]

lemma aligned_dot (d : ℝ) (z : Point) :
    sqDist z (d,0) = sqDist z 0 + d^2 - 2*d*z.1 := by
  simp [sqDist]
  ring

lemma cap_aligned {d : ℝ} (hd : 0 < d) (z : Point) :
    sqDist z (d,0)<sqDist z 0 ↔ d/2<z.1 := by
  rw [aligned_dot]
  have he : d^2-2*d*z.1 = 2*d*(d/2-z.1) := by ring
  rw [add_sub_assoc, he]
  constructor
  · intro h
    have hn : 2*d*(d/2-z.1)<0 := by linarith
    have hp : 0<2*d := by positivity
    have hz : d/2-z.1 < 0 := by
      by_contra! hh
      exact (not_lt_of_ge (mul_nonneg hp.le hh)) hn
    linarith
  · intro h
    have hn := mul_neg_of_pos_of_neg (show 0<2*d by positivity) (show d/2-z.1<0 by linarith)
    linarith

#print axioms shadow_rotate
#print axioms cap_aligned
end PermCircles
