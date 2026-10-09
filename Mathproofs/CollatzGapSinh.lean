import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Analytic core lemmas for the Collatz gap-factor argmin theorems (C22 / C23 / C25)

Source proofs: `~/workspace/math-unsolved/c22_proofs_r24.md`,
`~/workspace/math-unsolved/c23_proofs_r27.md`,
`~/workspace/math-unsolved/c25_proofs_r33.md`
(Round 37 of the continuous math-solving program, Lean formalization batch).

These three lemmas are the *analytic inputs* shared by all three gap-factor
theorems. They are stated and proved here in fully self-contained form,
independent of the Collatz / continued-fraction machinery:

- `gap_sinh_superlinear` — sub-lemma S: `sinh (k * z) > k * sinh z` for
  `z > 0` and integer `k ≥ 2`. Used in C22 Theorem 2, C23(a), C25 Theorem 1.
- `gap_sinh_le_mul_exp` — sub-lemma E: `sinh w ≤ w * exp (w ^ 2 / 6)` for
  `w ≥ 0`. Used in C22 Theorem 3, C23(b), C25 Theorem 2.
- `gap_log_one_add_ge` — `x / (1 + x) ≤ log (1 + x)` for `x > 0`.
  Used in the sufficient-condition cleanups of C23(b) and C25 Theorem 2.

Checked with Lean 4.34.1 + Mathlib v4.34.1, zero sorrys.
Remaining for the full batch: the exact Δ-sign criterion (C22 Lemma 1),
Δ strict monotonicity (C18b), the argmin-selection algebra, and the
C24 continued-fraction identity `ρ = 1 / α_{n+1}`.
-/

open NormedSpace
open scoped Nat

/-- Factorial growth bound: `6 ^ n * (n)! ≤ (2 * n + 1) !`.
The induction step needs `6 * (k+1) ≤ (2*k+3) * (2*k+2)`, i.e.
`0 ≤ 4 * k ^ 2 + 4 * k` (cf. the `(2j+3)/3 ≥ 1` ratio check in the hand proofs). -/
lemma six_pow_mul_factorial_le (n : ℕ) : 6 ^ n * (n)! ≤ (2 * n + 1)! := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have e1 : (2 * (k + 1) + 1)! = (2 * k + 3) * (2 * k + 2)! := by
      have h : 2 * (k + 1) + 1 = (2 * k + 2) + 1 := by ring
      rw [h, Nat.factorial_succ]
    have e2 : (2 * k + 2)! = (2 * k + 2) * (2 * k + 1)! := by
      have h : 2 * k + 2 = (2 * k + 1) + 1 := by ring
      rw [h, Nat.factorial_succ]
    have e3 : 6 ^ (k + 1) * (k + 1)! = 6 * (k + 1) * (6 ^ k * (k)!) := by
      rw [pow_succ, Nat.factorial_succ]
      ring
    have hle : 6 * (k + 1) ≤ (2 * k + 3) * (2 * k + 2) := by nlinarith [Nat.zero_le k]
    rw [e1, e2, e3]
    calc 6 * (k + 1) * (6 ^ k * (k)!)
        ≤ 6 * (k + 1) * (2 * k + 1)! := by gcongr
      _ = (6 * (k + 1)) * (2 * k + 1)! := by ring
      _ ≤ ((2 * k + 3) * (2 * k + 2)) * (2 * k + 1)! := by gcongr
      _ = (2 * k + 3) * ((2 * k + 2) * (2 * k + 1)!) := by ring

/-- Real-valued form of the factorial growth bound. -/
lemma six_pow_mul_factorial_le_real (n : ℕ) :
    (6 : ℝ) ^ n * ((n)! : ℝ) ≤ ((2 * n + 1)! : ℝ) := by
  exact_mod_cast six_pow_mul_factorial_le n

/-- Sub-lemma S (C22/C23/C25): `sinh` is strictly superlinear on `(0, ∞)`.
For `z > 0` and integer `k ≥ 2`: `sinh (k * z) > k * sinh z`.

Proof by induction on `k`: the base case `k = 2` uses
`sinh (2z) = 2 sinh z cosh z` with `cosh z > 1`; the step uses
`sinh ((k+1) z) = sinh (kz) cosh z + cosh (kz) sinh z` with both
`cosh` factors exceeding `1`. -/
theorem gap_sinh_superlinear (z : ℝ) (hz : 0 < z) (k : ℕ) (hk : 2 ≤ k) :
    (k : ℝ) * Real.sinh z < Real.sinh (k * z) := by
  induction k, hk using Nat.le_induction with
  | base =>
    have hcosh : (1 : ℝ) < Real.cosh z := Real.one_lt_cosh.mpr (ne_of_gt hz)
    have hsinh : (0 : ℝ) < Real.sinh z := ((Real.sinh_pos_iff.mpr hz))
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2, Real.sinh_two_mul]
    have h := mul_lt_mul_of_pos_left hcosh (show (0 : ℝ) < 2 * Real.sinh z by positivity)
    simpa using h
  | succ k hk ih =>
    have hcosh1 : (1 : ℝ) < Real.cosh z := Real.one_lt_cosh.mpr (ne_of_gt hz)
    have hkpos2 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hk
    have hkz : (0 : ℝ) < (k : ℝ) * z := mul_pos hkpos2 hz
    have hcoshkz : (1 : ℝ) < Real.cosh ((k : ℝ) * z) := Real.one_lt_cosh.mpr (ne_of_gt hkz)
    have hsinh : (0 : ℝ) < Real.sinh z := ((Real.sinh_pos_iff.mpr hz))
    have hkpos : (0 : ℝ) < (k : ℝ) * Real.sinh z := mul_pos hkpos2 hsinh
    have hcosh_pos : (0 : ℝ) < Real.cosh z := by linarith
    have step1 : (k : ℝ) * Real.sinh z < Real.sinh ((k : ℝ) * z) * Real.cosh z := by
      have a1 : (k : ℝ) * Real.sinh z * 1 < (k : ℝ) * Real.sinh z * Real.cosh z :=
        mul_lt_mul_of_pos_left hcosh1 hkpos
      have a2 : (k : ℝ) * Real.sinh z * Real.cosh z
          ≤ Real.sinh ((k : ℝ) * z) * Real.cosh z :=
        mul_le_mul_of_nonneg_right (le_of_lt ih) (le_of_lt hcosh_pos)
      have a1' : (k : ℝ) * Real.sinh z < (k : ℝ) * Real.sinh z * Real.cosh z := by
        linarith
      linarith
    have step2 : Real.sinh z < Real.cosh ((k : ℝ) * z) * Real.sinh z := by
      have b1 : (1 : ℝ) * Real.sinh z < Real.cosh ((k : ℝ) * z) * Real.sinh z :=
        mul_lt_mul_of_pos_right hcoshkz hsinh
      linarith
    have e1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have e2 : ((k : ℝ) + 1) * z = (k : ℝ) * z + z := by ring
    rw [e1, e2, Real.sinh_add]
    have hsum : ((k : ℝ) + 1) * Real.sinh z = (k : ℝ) * Real.sinh z + Real.sinh z := by
      ring
    rw [hsum]
    linarith

/-- Sub-lemma E (C22/C23/C25): `sinh w ≤ w * exp (w ^ 2 / 6)` for `w ≥ 0`.
Termwise from `sinh w = ∑ w ^ (2n+1) / (2n+1)!`, using
`(2n+1)! ≥ 6 ^ n * n!` (`six_pow_mul_factorial_le_real`) to dominate each
term by `w * (w ^ 2 / 6) ^ n / n!`. -/
theorem gap_sinh_le_mul_exp (w : ℝ) (hw : 0 ≤ w) :
    Real.sinh w ≤ w * Real.exp (w ^ 2 / 6) := by
  rw [Real.sinh_eq_tsum, Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ, ← tsum_mul_left]
  have hterm : ∀ n : ℕ, w ^ (2 * n + 1) / ((2 * n + 1)! : ℝ)
      ≤ w * (((((n)! : ℝ)))⁻¹ • (w ^ 2 / 6) ^ n) := by
    intro n
    have hfact : (6 : ℝ) ^ n * ((n)! : ℝ) ≤ ((2 * n + 1)! : ℝ) :=
      six_pow_mul_factorial_le_real n
    have hfact_pos : (0 : ℝ) < (6 : ℝ) ^ n * ((n)! : ℝ) :=
      mul_pos (pow_pos (by norm_num) n) (by exact_mod_cast Nat.factorial_pos n)
    have hnum_nn : (0 : ℝ) ≤ w * (w ^ 2) ^ n := by positivity
    have e1 : w ^ (2 * n + 1) = w * (w ^ 2) ^ n := by ring
    have e2 : w * (((((n)! : ℝ)))⁻¹ • (w ^ 2 / 6) ^ n)
        = w * (w ^ 2) ^ n / ((6 : ℝ) ^ n * ((n)! : ℝ)) := by
      rw [smul_eq_mul, div_pow, inv_mul_eq_div]
      ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_left hnum_nn hfact_pos hfact
  exact (Real.hasSum_sinh w).summable.tsum_le_tsum hterm
    ((expSeries_summable' (w ^ 2 / 6)).mul_left w)

/-- `x / (1 + x) ≤ log (1 + x)` for `x > 0`.
From `log (1 - t) ≤ -t` (`Real.log_le_sub_one_of_pos`) with
`t = x / (1 + x)`, i.e. `1 - t = (1 + x)⁻¹`. -/
theorem gap_log_one_add_ge (x : ℝ) (hx : 0 < x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h1ne : (1 : ℝ) + x ≠ 0 := ne_of_gt h1
  have ht1 : x / (1 + x) < 1 := by
    rw [div_lt_one h1]
    linarith
  have hlog : Real.log (1 - x / (1 + x)) ≤ -(x / (1 + x)) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - x / (1 + x) by linarith)
    linarith
  have hinv : (1 + x)⁻¹ = 1 - x / (1 + x) := by
    field_simp
    ring
  have heq : Real.log (1 + x) = -Real.log (1 - x / (1 + x)) := by
    rw [← hinv, Real.log_inv, neg_neg]
  linarith
