import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# C64/C64b hump-law: identity kernel + arithmetic closures

Source proofs: `~/workspace/math-unsolved/ROUND64_DOSSIER.md` (C64: strict
concavity of `t ↦ Q_t·d(Q_t)` on from-above blocks, every irrational α > 0)
and `~/workspace/math-unsolved/ROUND68_DOSSIER.md` (C64b: strict convexity on
from-below blocks, via the dual-weight hump law + 1−α transfer).

This module machine-checks the exact calculus identities and the numeric
bound closures at the heart of both proofs — the parts the dossiers flag as
"machine-checkable in a few lines":

- R64's φ-identity: `φ'(η) − ln2·φ(η) = (2^η−1)/2`
- R64's ψ-identity: `(ln2)²φ(η) − 2ln2·φ'(η) + φ''(η) = (ln2)/2`
- R68's dual identity: `ln2·Φ̃(η) + Φ̃'(η) = 1 − 2^{−η}`
- R68's dual ψ-identity: `(ln2)²Φ̃(η) + 2ln2·Φ̃'(η) + Φ̃''(η) = ln2`
- The 1−α transfer weight identity: `2^{1−s} = 2·2^{−s}`
- R64's closure: `c_Q` increasing for `Q ≥ 2`, `c_2 > 0` (the 0.08033)
- R68's closure: `c(Q)` increasing for `Q ≥ 3`, `c(3) > 0` (the 0.1189)

The full assembly (Abel summation, CF best-approximation / strict-record
lemma, block decomposition, mean-value second-difference estimates) is
staged for follow-up lanes; C64/C64b therefore remain [PROVED*] on paper
until that assembly is checked. Everything stated here is end-to-end
machine-checked: zero sorrys, `#print axioms` standard-only.

Checked with Lean 4.34.1 + Mathlib v4.34.1 (Round 121 of the continuous
math-solving program, Lean formalization lane).
-/

open Real

noncomputable section

/-- `0 < ln 2` (Mathlib has no `Real.log_two_pos`; this is `Real.log_pos`). -/
private lemma log_two_pos' : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- R64's correction function `φ(η) = (2^η(η·ln2−1)+1)/(2·ln2)`. -/
noncomputable def humpPhi (η : ℝ) : ℝ :=
  ((2:ℝ)^η * (Real.log 2 * η - 1) + 1) / (2 * Real.log 2)

/-- R68's dual correction function `Φ̃(η) = (1−2^{−η}(1+η·ln2))/ln2`. -/
noncomputable def humpPhiTilde (η : ℝ) : ℝ :=
  (1 - (2:ℝ)^(-η) * (1 + Real.log 2 * η)) / Real.log 2

/-- R64's uniform constant `D = max|d| = 1 − 1/(2·ln2)`. -/
noncomputable def humpD : ℝ := 1 - 1/(2 * Real.log 2)

/-- R68's dual uniform constant `D̃ = 2 − 1/ln2`. -/
noncomputable def humpDtilde : ℝ := 2 - 1/Real.log 2

/-- R64's closure constant `c_Q` (dossier §Step 2 conclusion). -/
noncomputable def humpC (Q : ℝ) : ℝ :=
  1/2 - humpD * Real.log 2 - (1 - (2:ℝ)^(-(1/Q))) / 2 - 0.480452/(3*Q)

/-- R68's closure constant `c(Q)` (dossier §Step 5). -/
noncomputable def humpCtilde (Q : ℝ) : ℝ :=
  1 - (2:ℝ)^(1/Q) * (Real.log 2 * humpDtilde)
    - ((2:ℝ)^(1/Q) - 1)
    - (2:ℝ)^(1/Q) * ((Real.log 2)^2 * humpDtilde + Real.log 2)/(3*Q)

section Derivatives

/-- Derivative of the constant-base exponential `η ↦ 2^η`. -/
lemma hasDerivAt_two_rpow (η : ℝ) :
    HasDerivAt (fun η => (2:ℝ)^η) (Real.log 2 * (2:ℝ)^η) η := by
  have hlin : HasDerivAt (fun η => Real.log 2 * η) (Real.log 2 * 1) η :=
    (hasDerivAt_id' η).const_mul (Real.log 2)
  have hexp := hlin.exp
  have hfun : ∀ x : ℝ, Real.exp (Real.log 2 * x) = (2:ℝ)^x := fun x =>
    (Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) x).symm
  have heq : Filter.EventuallyEq (nhds η) (fun η => (2:ℝ)^η)
      (fun x => Real.exp (Real.log 2 * x)) :=
    Filter.Eventually.of_forall (fun x => (hfun x).symm)
  have hexp2 := hexp.congr_of_eventuallyEq heq
  have hval : Real.exp (Real.log 2 * η) * (Real.log 2 * 1)
      = Real.log 2 * (2:ℝ)^η := by
    rw [hfun η]; ring
  rw [hval] at hexp2
  exact hexp2

/-- Derivative of the negated-base exponential `η ↦ 2^{−η}`. -/
lemma hasDerivAt_two_rpow_neg (η : ℝ) :
    HasDerivAt (fun η => (2:ℝ)^(-η)) (-(Real.log 2 * (2:ℝ)^(-η))) η := by
  have hlin : HasDerivAt (fun η => Real.log 2 * (-η)) (Real.log 2 * -1) η :=
    ((hasDerivAt_id' η).neg).const_mul (Real.log 2)
  have hexp := hlin.exp
  have hfun : ∀ x : ℝ, Real.exp (Real.log 2 * -x) = (2:ℝ)^(-x) := fun x =>
    (Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) (-x)).symm
  have heq : Filter.EventuallyEq (nhds η) (fun η => (2:ℝ)^(-η))
      (fun x => Real.exp (Real.log 2 * -x)) :=
    Filter.Eventually.of_forall (fun x => (hfun x).symm)
  have hexp2 := hexp.congr_of_eventuallyEq heq
  have hval : Real.exp (Real.log 2 * -η) * (Real.log 2 * -1)
      = -(Real.log 2 * (2:ℝ)^(-η)) := by
    rw [hfun η]; ring
  rw [hval] at hexp2
  exact hexp2

/-- `φ'(η) = η·ln2·2^η/2`. -/
lemma humpPhi_hasDerivAt (η : ℝ) :
    HasDerivAt humpPhi (η * Real.log 2 * (2:ℝ)^η / 2) η := by
  have h2 := hasDerivAt_two_rpow η
  have hlin : HasDerivAt (fun η => Real.log 2 * η - 1) (Real.log 2) η := by
    have h := ((hasDerivAt_id' η).const_mul (Real.log 2)).sub (hasDerivAt_const η (1:ℝ))
    simp only [mul_one, sub_zero] at h
    exact h
  have hN : HasDerivAt (fun η => (2:ℝ)^η * (Real.log 2 * η - 1) + 1)
      ((Real.log 2 * (2:ℝ)^η) * (Real.log 2 * η - 1) + (2:ℝ)^η * Real.log 2) η := by
    have h := (h2.mul hlin).add (hasDerivAt_const η (1:ℝ))
    beta_reduce at h
    simp only [add_zero] at h
    exact h
  have hdiv := hN.div_const (2 * Real.log 2)
  have hval : ((Real.log 2 * (2:ℝ)^η) * (Real.log 2 * η - 1) + (2:ℝ)^η * Real.log 2)
        / (2 * Real.log 2) = η * Real.log 2 * (2:ℝ)^η / 2 := by
    have hne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos'
    field_simp
    ring
  rw [hval] at hdiv
  exact hdiv

/-- `φ''(η) = ln2·2^η·(1+η·ln2)/2`. -/
lemma humpPhi_second (η : ℝ) :
    HasDerivAt (fun η => η * Real.log 2 * (2:ℝ)^η / 2)
      (Real.log 2 * (2:ℝ)^η * (1 + η * Real.log 2) / 2) η := by
  have h2 := hasDerivAt_two_rpow η
  have hA : HasDerivAt (fun η => η * Real.log 2) (Real.log 2) η := by
    have h := (hasDerivAt_id' η).mul_const (Real.log 2)
    simp only [one_mul] at h
    exact h
  have hB : HasDerivAt (fun η => η * Real.log 2 * (2:ℝ)^η)
      (Real.log 2 * (2:ℝ)^η + η * Real.log 2 * (Real.log 2 * (2:ℝ)^η)) η := by
    have h := hA.mul h2
    beta_reduce at h
    exact h
  have hC := hB.div_const (2:ℝ)
  have hval : (Real.log 2 * (2:ℝ)^η + η * Real.log 2 * (Real.log 2 * (2:ℝ)^η)) / 2
      = Real.log 2 * (2:ℝ)^η * (1 + η * Real.log 2) / 2 := by ring
  rw [hval] at hC
  exact hC

/-- `Φ̃'(η) = η·ln2·2^{−η}`. -/
lemma humpPhiTilde_hasDerivAt (η : ℝ) :
    HasDerivAt humpPhiTilde (η * Real.log 2 * (2:ℝ)^(-η)) η := by
  have h2n := hasDerivAt_two_rpow_neg η
  have hlin : HasDerivAt (fun η => 1 + Real.log 2 * η) (Real.log 2) η := by
    have h := (hasDerivAt_const η (1:ℝ)).add ((hasDerivAt_id' η).const_mul (Real.log 2))
    simp only [zero_add, mul_one] at h
    exact h
  have hM : HasDerivAt (fun η => (2:ℝ)^(-η) * (1 + Real.log 2 * η))
      ((-(Real.log 2 * (2:ℝ)^(-η))) * (1 + Real.log 2 * η)
        + (2:ℝ)^(-η) * Real.log 2) η :=
    h2n.mul hlin
  have hsub : HasDerivAt (fun η => 1 - (2:ℝ)^(-η) * (1 + Real.log 2 * η))
      (0 - ((-(Real.log 2 * (2:ℝ)^(-η))) * (1 + Real.log 2 * η)
        + (2:ℝ)^(-η) * Real.log 2)) η :=
    (hasDerivAt_const η (1:ℝ)).sub hM
  have hdiv := hsub.div_const (Real.log 2)
  have hval : (0 - ((-(Real.log 2 * (2:ℝ)^(-η))) * (1 + Real.log 2 * η)
        + (2:ℝ)^(-η) * Real.log 2)) / Real.log 2
      = η * Real.log 2 * (2:ℝ)^(-η) := by
    have hne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos'
    field_simp
    ring
  rw [hval] at hdiv
  exact hdiv

/-- `Φ̃''(η) = ln2·2^{−η}·(1−η·ln2)`. -/
lemma humpPhiTilde_second (η : ℝ) :
    HasDerivAt (fun η => η * Real.log 2 * (2:ℝ)^(-η))
      (Real.log 2 * (2:ℝ)^(-η) * (1 - η * Real.log 2)) η := by
  have h2n := hasDerivAt_two_rpow_neg η
  have hA : HasDerivAt (fun η => η * Real.log 2) (Real.log 2) η := by
    have h := (hasDerivAt_id' η).mul_const (Real.log 2)
    simp only [one_mul] at h
    exact h
  have hB : HasDerivAt (fun η => η * Real.log 2 * (2:ℝ)^(-η))
      (Real.log 2 * (2:ℝ)^(-η) + η * Real.log 2 * (-(Real.log 2 * (2:ℝ)^(-η)))) η :=
    hA.mul h2n
  have hval : Real.log 2 * (2:ℝ)^(-η) + η * Real.log 2 * (-(Real.log 2 * (2:ℝ)^(-η)))
      = Real.log 2 * (2:ℝ)^(-η) * (1 - η * Real.log 2) := by ring
  rw [hval] at hB
  exact hB

end Derivatives

section Identities

/-- R64's φ-identity: `φ'(η) − ln2·φ(η) = (2^η−1)/2` (3-line calculus). -/
lemma humpPhi_identity (η : ℝ) :
    (η * Real.log 2 * (2:ℝ)^η / 2) - Real.log 2 * humpPhi η
      = ((2:ℝ)^η - 1) / 2 := by
  have hne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos'
  unfold humpPhi
  field_simp
  ring

/-- R64's ψ-identity: `(ln2)²φ(η) − 2ln2·φ'(η) + φ''(η) = (ln2)/2`. -/
lemma humpPsi_identity (η : ℝ) :
    (Real.log 2)^2 * humpPhi η
      - 2 * Real.log 2 * (η * Real.log 2 * (2:ℝ)^η / 2)
      + (Real.log 2 * (2:ℝ)^η * (1 + η * Real.log 2) / 2)
      = Real.log 2 / 2 := by
  have hne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos'
  unfold humpPhi
  field_simp
  ring

/-- R68's dual first identity: `ln2·Φ̃(η) + Φ̃'(η) = 1 − 2^{−η}`. -/
lemma humpPhiTilde_identity (η : ℝ) :
    Real.log 2 * humpPhiTilde η + η * Real.log 2 * (2:ℝ)^(-η)
      = 1 - (2:ℝ)^(-η) := by
  have hne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos'
  unfold humpPhiTilde
  field_simp
  ring

/-- R68's dual ψ-identity: `(ln2)²Φ̃(η) + 2ln2·Φ̃'(η) + Φ̃''(η) = ln2`. -/
lemma humpPsiTilde_identity (η : ℝ) :
    (Real.log 2)^2 * humpPhiTilde η
      + 2 * Real.log 2 * (η * Real.log 2 * (2:ℝ)^(-η))
      + (Real.log 2 * (2:ℝ)^(-η) * (1 - η * Real.log 2))
      = Real.log 2 := by
  have hne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos'
  unfold humpPhiTilde
  field_simp
  ring

/-- R68's transfer weight identity: `2^{1−s} = 2·2^{−s}`
(whence `S̃_{1−α}(q) = 2S_α(q) − 1`). -/
lemma dual_weight_transfer (s : ℝ) : (2:ℝ)^(1 - s) = 2 * (2:ℝ)^(-s) := by
  rw [show (1:ℝ) - s = 1 + -s by ring,
    Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]

end Identities

section NumericBounds

/-- `2^{−1/2} ≥ 0.7071` (for the C64 closure at `Q = 2`). -/
lemma two_rpow_neg_half_ge : (0.7071:ℝ) ≤ (2:ℝ)^(-(1/2):ℝ) := by
  have hsq : ((2:ℝ)^(-(1/2):ℝ))^2 = 1/2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      Nat.cast_ofNat, show (-(1/2) : ℝ) * 2 = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  have hy : (0:ℝ) ≤ (2:ℝ)^(-(1/2):ℝ) := Real.rpow_nonneg (by norm_num) _
  have h2 : (0.7071:ℝ)^2 ≤ ((2:ℝ)^(-(1/2):ℝ))^2 := by rw [hsq]; norm_num
  nlinarith [h2, hy, sq_nonneg ((2:ℝ)^(-(1/2):ℝ) - 0.7071)]

/-- `2^{1/3} ≤ 1.26` (for the dual closure at `Q = 3`). -/
lemma two_rpow_third_le : (2:ℝ)^((1/3):ℝ) ≤ 1.26 := by
  have hcube : ((2:ℝ)^((1/3):ℝ))^3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      Nat.cast_ofNat, show ((1/3):ℝ) * 3 = 1 by norm_num, Real.rpow_one]
  have hy : (0:ℝ) ≤ (2:ℝ)^((1/3):ℝ) := Real.rpow_nonneg (by norm_num) _
  have h3 : ((2:ℝ)^((1/3):ℝ))^3 ≤ (1.26:ℝ)^3 := by rw [hcube]; norm_num
  have hfac : ((2:ℝ)^((1/3):ℝ) - 1.26)
        * (((2:ℝ)^((1/3):ℝ))^2 + (2:ℝ)^((1/3):ℝ)*1.26 + 1.26^2)
      = ((2:ℝ)^((1/3):ℝ))^3 - 1.26^3 := by ring
  have hpos : (0:ℝ) < ((2:ℝ)^((1/3):ℝ))^2 + (2:ℝ)^((1/3):ℝ)*1.26 + 1.26^2 := by
    have h1 := sq_nonneg ((2:ℝ)^((1/3):ℝ))
    have h2 := mul_nonneg hy (show (0:ℝ) ≤ 1.26 by norm_num)
    nlinarith
  nlinarith [h3, hfac, hpos]

end NumericBounds

section Closures

lemma humpD_pos : 0 < humpD := by
  unfold humpD
  rw [sub_pos, div_lt_one (by linarith [log_two_pos'] : (0:ℝ) < 2 * Real.log 2)]
  linarith [Real.log_two_gt_d9]

lemma humpDtilde_pos : 0 < humpDtilde := by
  unfold humpDtilde
  rw [sub_pos, div_lt_iff₀ log_two_pos']
  linarith [Real.log_two_gt_d9]

/-- `D·ln2 = ln2 − 1/2`. -/
lemma humpLD_identity : humpD * Real.log 2 = Real.log 2 - 1/2 := by
  have hne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos'
  unfold humpD
  field_simp

/-- `ln2·D̃ = 2·ln2 − 1`. -/
lemma humpLDtilde_identity : Real.log 2 * humpDtilde = 2 * Real.log 2 - 1 := by
  have hne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos'
  unfold humpDtilde
  field_simp

/-- The K-identity: `(ln2)²D̃ + ln2 = 2(ln2)²`. -/
lemma humpK_identity :
    (Real.log 2)^2 * humpDtilde + Real.log 2 = 2 * (Real.log 2)^2 := by
  have hne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos'
  unfold humpDtilde
  field_simp
  ring

/-- R64's `c_Q` is increasing for `Q ≥ 2`. -/
lemma humpC_mono {Q₁ Q₂ : ℝ} (h1 : 2 ≤ Q₁) (h2 : Q₁ ≤ Q₂) :
    humpC Q₁ ≤ humpC Q₂ := by
  have hQ₁ : (0:ℝ) < Q₁ := by linarith
  have hQ₂ : (0:ℝ) < Q₂ := by linarith
  have hexp : (2:ℝ)^(-(1/Q₁)) ≤ (2:ℝ)^(-(1/Q₂)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (neg_le_neg (one_div_le_one_div_of_le hQ₁ h2))
  have hfrac : (0.480452:ℝ)/(3*Q₂) ≤ 0.480452/(3*Q₁) := by
    have h := one_div_le_one_div_of_le (by linarith : (0:ℝ) < 3*Q₁) (by linarith : 3*Q₁ ≤ 3*Q₂)
    have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 0.480452)
    rw [mul_one_div, mul_one_div] at h2
    exact h2
  unfold humpC
  linarith [hexp, hfrac]

/-- R64's closure at `Q = 2`: `c_2 = 0.08033… > 0`. -/
lemma humpC_two_pos : 0 < humpC 2 := by
  have hL := Real.log_two_lt_d9
  have hr := two_rpow_neg_half_ge
  have hb : (0.480452:ℝ)/(3*2) < 0.08008 := by norm_num
  unfold humpC
  rw [humpLD_identity]
  linarith

/-- R68's `c(Q)` is increasing for `Q ≥ 3` (each subtracted term shrinks as
`2^{1/Q}` falls; the dossier's "decreasing" is a direction slip — the
subtractions decrease, so `c` increases; `c(3)` is the minimum). -/
lemma humpCtilde_mono {Q₁ Q₂ : ℝ} (h1 : 3 ≤ Q₁) (h2 : Q₁ ≤ Q₂) :
    humpCtilde Q₁ ≤ humpCtilde Q₂ := by
  have hQ₁ : (0:ℝ) < Q₁ := by linarith
  have hQ₂ : (0:ℝ) < Q₂ := by linarith
  have hexp : (2:ℝ)^(1/Q₂) ≤ (2:ℝ)^(1/Q₁) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (one_div_le_one_div_of_le hQ₁ h2)
  have hLD : (0:ℝ) < Real.log 2 * humpDtilde := by
    rw [humpLDtilde_identity]; linarith [Real.log_two_gt_d9]
  have hK : (0:ℝ) < (Real.log 2)^2 * humpDtilde + Real.log 2 := by
    rw [humpK_identity]; exact mul_pos (by norm_num) (pow_pos log_two_pos' 2)
  have ht1 : (2:ℝ)^(1/Q₂) * (Real.log 2 * humpDtilde)
      ≤ (2:ℝ)^(1/Q₁) * (Real.log 2 * humpDtilde) :=
    mul_le_mul_of_nonneg_right hexp (le_of_lt hLD)
  have ht2 : (2:ℝ)^(1/Q₂) - 1 ≤ (2:ℝ)^(1/Q₁) - 1 := by linarith [hexp]
  have ht3 : (2:ℝ)^(1/Q₂) * ((Real.log 2)^2 * humpDtilde + Real.log 2)/(3*Q₂)
      ≤ (2:ℝ)^(1/Q₁) * ((Real.log 2)^2 * humpDtilde + Real.log 2)/(3*Q₁) := by
    have hnum : (2:ℝ)^(1/Q₂) * ((Real.log 2)^2 * humpDtilde + Real.log 2)
        ≤ (2:ℝ)^(1/Q₁) * ((Real.log 2)^2 * humpDtilde + Real.log 2) :=
      mul_le_mul_of_nonneg_right hexp (le_of_lt hK)
    have hnn₂ : (0:ℝ) ≤ (3*Q₂)⁻¹ :=
      inv_nonneg.mpr (by linarith : (0:ℝ) ≤ 3*Q₂)
    have hnn₁ : (0:ℝ) ≤ (2:ℝ)^(1/Q₁) * ((Real.log 2)^2 * humpDtilde + Real.log 2) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (le_of_lt hK)
    have hinv : (3*Q₂)⁻¹ ≤ (3*Q₁)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by linarith : (0:ℝ) < 3*Q₁) (by linarith : 3*Q₁ ≤ 3*Q₂)
    have h1 := mul_le_mul hnum hinv hnn₂ hnn₁
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact h1
  unfold humpCtilde
  linarith [ht1, ht2, ht3]

/-- R68's closure at `Q = 3`: `c(3) = 0.1189… > 0`. -/
lemma humpCtilde_three_pos : 0 < humpCtilde 3 := by
  have hL := Real.log_two_lt_d9
  have ht := two_rpow_third_le
  have hL2 : (Real.log 2)^2 < (0.6931471808:ℝ)^2 := by
    nlinarith [Real.log_two_lt_d9, log_two_pos']
  have hS : 2 * Real.log 2 + 2 * (Real.log 2)^2/9 < 1.4930617 := by
    linarith [hL, hL2]
  have hprod : (2:ℝ)^((1/3):ℝ) * (2 * Real.log 2 + 2 * (Real.log 2)^2/9) < 2 := by
    have hnn : (0:ℝ) ≤ 2 * Real.log 2 + 2 * (Real.log 2)^2/9 := by
      have h1 : (0:ℝ) ≤ 2 * (Real.log 2)^2/9 := by positivity
      nlinarith [log_two_pos']
    have hS' := le_of_lt hS
    calc (2:ℝ)^((1/3):ℝ) * (2 * Real.log 2 + 2 * (Real.log 2)^2/9)
        ≤ 1.26 * (2 * Real.log 2 + 2 * (Real.log 2)^2/9) :=
          mul_le_mul_of_nonneg_right ht hnn
      _ ≤ 1.26 * 1.4930617 := by gcongr
      _ < 2 := by norm_num
  unfold humpCtilde
  rw [humpLDtilde_identity, humpK_identity]
  linarith [hprod]

end Closures

end
