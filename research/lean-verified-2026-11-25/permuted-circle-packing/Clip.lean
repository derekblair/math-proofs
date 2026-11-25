import Mathlib.Tactic

namespace PermCircles

abbrev Point := ℝ × ℝ

def sqDist (a b : Point) : ℝ := (a.1-b.1)^2+(a.2-b.2)^2

lemma three_radial {r : ℝ} {a b c z : Point}
    (hab : 4*r^2 ≤ sqDist a b) (hac : 4*r^2 ≤ sqDist a c)
    (hbc : 4*r^2 ≤ sqDist b c)
    (ha : sqDist a z ≤ 4*r^2/3) (hb : sqDist b z ≤ 4*r^2/3)
    (hc : sqDist c z < 4*r^2/3) : False := by
  have he :
    sqDist a b+sqDist a c+sqDist b c =
      3*(sqDist a z+sqDist b z+sqDist c z) -
       ((a.1+b.1+c.1-3*z.1)^2+(a.2+b.2+c.2-3*z.2)^2) := by
    unfold sqDist
    ring
  linarith [sq_nonneg (a.1+b.1+c.1-3*z.1),sq_nonneg (a.2+b.2+c.2-3*z.2)]

def dotDir (a z : Point) : ℝ := a.1*z.1 + a.2*z.2

def radialShadow (ρ : ℝ) (b z : Point) : Prop :=
  0 < sqDist z 0 ∧ sqDist z 0 ≤ ρ^2 ∧
    sqDist ((ρ / Real.sqrt (sqDist z 0)) • z) b < ρ^2

lemma radial_sq (ρ : ℝ) {z : Point} (hz : 0 < sqDist z 0) :
    sqDist ((ρ / Real.sqrt (sqDist z 0)) • z) 0 = ρ^2 := by
  have hh := Real.sq_sqrt (le_of_lt hz)
  have h0 : Real.sqrt (sqDist z 0) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hz)
  have hs (t : ℝ) : sqDist (t • z) 0 = t^2 * sqDist z 0 := by
    simp [sqDist]
    ring
  rw [hs,div_pow]
  conv_lhs => arg 2; rw [← hh]
  exact div_mul_cancel₀ _ (pow_ne_zero 2 h0)

lemma sqDist_symm (a b : Point) : sqDist a b = sqDist b a := by
  unfold sqDist
  ring

lemma shadows_separate {r ρ : ℝ} (hρ : ρ^2 = 4*r^2/3) {b c z : Point}
    (hb : 4*r^2 ≤ sqDist 0 b) (hc : 4*r^2 ≤ sqDist 0 c)
    (hbc : 4*r^2 ≤ sqDist b c) (h1 : radialShadow ρ b z) (h2 : radialShadow ρ c z) : False := by
  let w := (ρ / Real.sqrt (sqDist z 0)) • z
  have h0 : sqDist w 0 = ρ^2 := radial_sq ρ h1.1
  have hwb : sqDist w b < ρ^2 := h1.2.2
  have hwc : sqDist w c < ρ^2 := h2.2.2
  rw [sqDist_symm w 0,hρ] at h0
  rw [sqDist_symm w b,hρ] at hwb
  rw [sqDist_symm w c,hρ] at hwc
  exact three_radial hb hc hbc (le_of_eq h0) (le_of_lt hwb) hwc

lemma cap_in_shadow {ρ : ℝ} {b z : Point} (hρ : 0 < ρ)
    (hz : sqDist z 0 ≤ ρ^2) (h : sqDist z b < sqDist z 0) :
    radialShadow ρ b z := by
  have hE (a : Point) : sqDist a b = sqDist a 0+sqDist b 0-2*dotDir b a := by
    unfold sqDist dotDir
    simp
    ring
  have hb0 : 0 ≤ sqDist b 0 := by exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hz0 : 0 < sqDist z 0 := by
    by_contra! hn
    have hh : 0 ≤ sqDist z b := add_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  have hdot : 0 < dotDir b z := by rw [hE z] at h; linarith
  let t := ρ / Real.sqrt (sqDist z 0)
  have ht : 1 ≤ t := by
    exact (le_div_iff₀ (Real.sqrt_pos.2 hz0)).2 (by
      simp only [one_mul]
      exact Real.sqrt_le_iff.mpr ⟨hρ.le,hz⟩)
  have he : dotDir b (t • z) = t*dotDir b z := by simp [dotDir]; ring
  refine ⟨hz0,hz,?_⟩
  change sqDist (t • z) b < ρ^2
  rw [hE,radial_sq ρ hz0,he]
  have hmul : 0 ≤ (t-1)*dotDir b z := mul_nonneg (by linarith) hdot.le
  rw [hE z] at h
  nlinarith

#print axioms shadows_separate
end PermCircles
