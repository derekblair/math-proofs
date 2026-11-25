/-
  AbsorbedBound.lean — Corrected R200 T4: absorbed + R|30030 ⟹ c ≤ 320 (self-bound).

  Paper: papers/hole-suppression-absorption-October-11-2026/
  Status: [PROVED] — t4_self_bound (+ R-arithmetic API)
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R250: exit 0 both sides, zero sorrys, axioms [propext, Classical.choice, Quot.sound] (standard).
-/

/-
R200 — Absorbed 13|h regime: T4 self-bound c≤320 (ROUND200_DOSSIER.md §2).

Claims formalised (machine-checked):
- `R_dvd_2310` / `R_le_2310`: R|30030 with 13∤R gives R|2310, hence R≤2310
  (30030 = 13·2310).
- `a_mul_m_le`: the a ≤ 2R/m bound in multiplicative form (a*m ≤ 2*R),
  from a≤b and a+b=m·h.
- `a_sq_eq`: the parametrization identity a² = g*(m*h₁*a − R), where
  g=gcd(ab,h), h=g*h₁, R=ab/g.
- `t_pos` / `t_le_R`: for t := m*h₁*a − R, 1 ≤ t ≤ R.
- `hmt_eq`: the exact relation h*m*t = a*(t+R).
- `h_mul_sq_le`: h*m² ≤ 4*R².
- `t4_self_bound`: absorbed (13|h, 13∤R, R|30030) ⟹ c ≤ 320.
T2 (trichotomy extension) and T3 (fiber-extruded slice) need the
κ/ρ/g₀ apparatus — reviewed (see review-r200/) but formalization pending
that apparatus. T5′ is [PROVED] in AbsorbedRegime.lean (ROUND222).

Requires hostile review clearance per PROGRAM.md rule 9 before [PROVED].

Checked: Lean 4.34.1 + Mathlib v4.34.1, `lake build`, zero sorrys,
`#print axioms` standard-only.
-/
import Mathlib

namespace AbsorbedBound

/-- 30030 = 13·2310, and 13∤R forces R|2310 (Euclid). -/
theorem R_dvd_2310 (R : ℤ) (hRdiv : R ∣ 30030) (h13R : ¬ (13:ℤ) ∣ R) :
    R ∣ 2310 := by
  obtain ⟨k, hk⟩ := hRdiv
  have h13prime : Prime (13:ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
  have h13dvd : (13:ℤ) ∣ R * k := ⟨2310, by linarith [hk]⟩
  have hdisj : (13:ℤ) ∣ R ∨ (13:ℤ) ∣ k := (h13prime.dvd_mul).mp h13dvd
  rcases hdisj with h | h
  · exact absurd h h13R
  · obtain ⟨k', hk'⟩ := h
    refine ⟨k', ?_⟩
    have h30030 : (30030:ℤ) = 13 * 2310 := by norm_num
    have e3 : R * k = 13 * (R * k') := by rw [hk']; ring
    rw [← hk, h30030] at e3
    exact mul_left_cancel₀ (show (13:ℤ) ≠ 0 by norm_num) e3

/-- R ≤ 2310 for positive R. -/
theorem R_le_2310 (R : ℤ) (hRpos : 1 ≤ R) (hRdiv : R ∣ 2310) : R ≤ 2310 := by
  have h := Int.le_of_dvd (by norm_num : (0:ℤ) < 2310) hRdiv
  omega

/-- The a ≤ 2R/m bound (multiplicative form): from a≤b and a+b=m·h,
    using ab=R·g and h=g·h₁. -/
theorem a_mul_m_le (a b m h R g h₁ : ℤ)
    (ha : 1 ≤ a) (hmpos : 1 ≤ m)
    (hab : a + b = m * h) (hle : a ≤ b)
    (hg : 1 ≤ g) (hh1pos : 1 ≤ h₁)
    (hR : a * b = R * g) (hh : h = g * h₁) :
    a * m ≤ 2 * R := by
  have h1 : a ^ 2 ≤ a * b := by
    have hle' : a * a ≤ a * b := mul_le_mul_of_nonneg_left hle (by omega)
    rwa [pow_two]
  have h3 : a * (m * h) ≤ 2 * (a * b) := by
    have h2 : a * (m * h) = a ^ 2 + a * b := by
      have e : a * (m * h) = a * (a + b) := by rw [hab]
      rw [e]; ring
    linarith [h1, h2]
  have h4 : (a * m * h₁) * g ≤ (2 * R) * g := by
    have e1 : (a * m * h₁) * g = a * (m * h) := by rw [hh]; ring
    have e2 : (2 * R) * g = 2 * (a * b) := by rw [mul_assoc, hR]
    rw [e1, e2]; exact h3
  have h5 : a * m * h₁ ≤ 2 * R :=
    le_of_mul_le_mul_right h4 (show (0:ℤ) < g by omega)
  calc a * m = (a * m) * 1 := by ring
    _ ≤ (a * m) * h₁ :=
        mul_le_mul_of_nonneg_left hh1pos
          (mul_nonneg (by omega) (by omega))
    _ = a * m * h₁ := by ring
    _ ≤ 2 * R := h5

/-- Parametrization identity: a² = g*(m*h₁*a − R). -/
theorem a_sq_eq (a b m h R g h₁ : ℤ)
    (hab : a + b = m * h)
    (hR : a * b = R * g) (hh : h = g * h₁) :
    a ^ 2 = g * (m * h₁ * a - R) := by
  have e1 : a * (a + b) = a * (m * h) := by rw [hab]
  have e2 : a * (m * h) = g * (m * h₁ * a) := by rw [hh]; ring
  have e3 : a * (a + b) = a ^ 2 + a * b := by ring
  linear_combination -e3 + e1 + e2 - hR

/-- The parameter t := m*h₁*a − R is positive. -/
theorem t_pos (a m R g h₁ : ℤ) (ha : 1 ≤ a) (hg : 1 ≤ g)
    (hA2 : a ^ 2 = g * (m * h₁ * a - R)) :
    1 ≤ m * h₁ * a - R := by
  by_contra hcon
  push_neg at hcon
  have hle : g * (m * h₁ * a - R) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  have hsq : (1:ℤ) ≤ a ^ 2 := by nlinarith [ha]
  linarith [hA2, hle, hsq]

/-- The parameter t satisfies t ≤ R (from a ≤ b). -/
theorem t_le_R (a b m R g h₁ : ℤ) (ha : 1 ≤ a) (hle : a ≤ b) (hg : 1 ≤ g)
    (hR : a * b = R * g) (hA2 : a ^ 2 = g * (m * h₁ * a - R)) :
    m * h₁ * a - R ≤ R := by
  have h1 : a * a ≤ a * b := mul_le_mul_of_nonneg_left hle (by omega)
  have h2 : g * (m * h₁ * a - R) ≤ R * g := by
    have e : g * (m * h₁ * a - R) = a * a := by rw [← hA2, pow_two]
    rw [e]
    calc a * a ≤ a * b := h1
      _ = R * g := hR
  by_contra hcon
  push_neg at hcon
  have hlt := mul_lt_mul_of_pos_left hcon (show (0:ℤ) < g by omega)
  linarith [hlt, h2]

/-- Exact relation h*m*t = a*(t+R). -/
theorem hmt_eq (a m h R g h₁ : ℤ)
    (hh : h = g * h₁)
    (hA2 : a ^ 2 = g * (m * h₁ * a - R)) :
    h * m * (m * h₁ * a - R) = a * ((m * h₁ * a - R) + R) := by
  have e1 : (m * h₁ * a - R) + R = m * h₁ * a := by ring
  rw [e1]
  calc h * m * (m * h₁ * a - R)
      = (g * h₁) * m * (m * h₁ * a - R) := by rw [hh]
    _ = (g * (m * h₁ * a - R)) * (m * h₁) := by ring
    _ = (a ^ 2) * (m * h₁) := by rw [hA2]
    _ = a * (m * h₁ * a) := by ring

/-- The h-bound: h*m² ≤ 4*R². -/
theorem h_mul_sq_le (a m h R t : ℤ)
    (hhpos : 1 ≤ h) (hmpos : 1 ≤ m)
    (ht1 : 1 ≤ t) (htR : t ≤ R) (hRpos : 1 ≤ R)
    (ham : a * m ≤ 2 * R)
    (hmt : h * m * t = a * (t + R)) :
    h * m ^ 2 ≤ 4 * R ^ 2 := by
  have e1 : (h * m ^ 2) * t = (a * m) * (t + R) := by
    calc (h * m ^ 2) * t = (h * m * t) * m := by ring
      _ = (a * (t + R)) * m := by rw [hmt]
      _ = (a * m) * (t + R) := by ring
  have e2 : (a * m) * (t + R) ≤ (2 * R) * (2 * R) :=
    mul_le_mul ham (by linarith [htR]) (by linarith [ht1, hRpos])
      (by linarith [hRpos])
  have e3 : h * m ^ 2 ≤ (h * m ^ 2) * t := by
    calc h * m ^ 2 = (h * m ^ 2) * 1 := by ring
      _ ≤ (h * m ^ 2) * t :=
          mul_le_mul_of_nonneg_left ht1
            (mul_nonneg (by omega) (by positivity))
  have e4 : (h * m ^ 2) * t ≤ 4 * R ^ 2 := by linarith [e1, e2]
  linarith [e3, e4]

/-- T4 (R200): absorbed (13|h, 13∤R, R|30030) ⟹ c ≤ 320. -/
theorem t4_self_bound (c h a b m R g h₁ : ℤ)
    (hc : 1 ≤ c) (hh : 1 ≤ h) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : m = 4 * c - 1)
    (hab : a + b = m * h) (hle : a ≤ b)
    (hg : 1 ≤ g)
    (hR : a * b = R * g) (hh1 : h = g * h₁) (hh1pos : 1 ≤ h₁)
    (hRpos : 1 ≤ R) (hRdiv : R ∣ 30030) (h13R : ¬ (13:ℤ) ∣ R) (h13h : 13 ∣ h) :
    c ≤ 320 := by
  have hmpos : 1 ≤ m := by omega
  have hR2310 := R_dvd_2310 R hRdiv h13R
  have hRle := R_le_2310 R hRpos hR2310
  have ham := a_mul_m_le a b m h R g h₁ ha hmpos hab hle hg hh1pos hR hh1
  have hA2 := a_sq_eq a b m h R g h₁ hab hR hh1
  have ht1 := t_pos a m R g h₁ ha hg hA2
  have htR := t_le_R a b m R g h₁ ha hle hg hR hA2
  have hmt := hmt_eq a m h R g h₁ hh1 hA2
  have h4 := h_mul_sq_le a m h R (m * h₁ * a - R) hh hmpos ht1 htR hRpos ham hmt
  have h13m : (13:ℤ) * m ^ 2 ≤ 4 * R ^ 2 := by
    have h13le : (13:ℤ) ≤ h := by
      obtain ⟨k, hk⟩ := h13h
      have hk1 : 1 ≤ k := by omega
      omega
    have hle2 : (13:ℤ) * m ^ 2 ≤ h * m ^ 2 :=
      mul_le_mul_of_nonneg_right h13le (by positivity)
    linarith [hle2, h4]
  have hm1281 : m ≤ 1281 := by
    by_contra hcon
    push_neg at hcon
    have hsq : (1282:ℤ) ^ 2 ≤ m ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by omega) 2
    have h6 : (13:ℤ) * 1282 ^ 2 ≤ 13 * m ^ 2 := by linarith [hsq]
    have h7 : 4 * R ^ 2 ≤ 4 * 2310 ^ 2 := by
      have hR2 : R ^ 2 ≤ 2310 ^ 2 := pow_le_pow_left₀ (by omega) hRle 2
      linarith [hR2]
    linarith [h13m, h6, h7]
  omega
