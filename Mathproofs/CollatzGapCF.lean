import Mathlib

/-!
# Complete-quotient API and the continued-fraction error formula (C24 Lemma 1)

Source proofs: `~/workspace/math-unsolved/c24_proofs_r30.md`
(Round 49 of the continuous math-solving program, Lean formalization batch).

Mathlib 4.34.1 has **no** complete-quotient API (its `GenContFract` machinery
carries no real-error formula), so we build the needed vocabulary from scratch:

- `cquot` — complete quotients `α₀ = α`, `αₙ₊₁ = 1 / fract αₙ`;
- `pquot` — partial quotients `aₙ = ⌊αₙ⌋`;
- `cnum`, `cden` — convergent numerators `pₙ` / denominators `qₙ`;
- `cerr` — signed error `eₙ = α qₙ − pₙ` (so `δₙ = |eₙ|`).

Main results (all for irrational `α`):

- `cf_error_formula` — `|eₙ₊₁| = 1 / (αₙ₊₂ qₙ₊₁ + qₙ)` (C24 Lemma 1, first part);
- `cf_ratio_formula` — `|eₙ₊₁| / |eₙ| = 1 / αₙ₊₂`, i.e. `ρₙ = 1 / αₙ₊₁`
  (C24 Lemma 1, the error-ratio identity);
- `cf_det_identity` — for even `m`: `qₘ₊₁ |eₘ| + qₘ |eₘ₊₁| = 1`
  (the `(F1)` input `qₙ δₙ₋₁ + qₙ₋₁ δₙ = 1` for the C22/C23/C25 assembly).

Proof strategy: the error recurrence `αₙ₊₂ eₙ₊₁ = −eₙ` (by induction, using
`αₙ₊₁ = aₙ₊₁ + 1/αₙ₊₂`) plus the determinant identity
`eₙ qₙ₊₁ − eₙ₊₁ qₙ = (−1)ⁿ` combine to give the error formula; the ratio
follows from the algebraic identity
`αₙ₊₂ (αₙ₊₁ qₙ + qₙ₋₁) = αₙ₊₂ qₙ₊₁ + qₙ`.

Checked with Lean 4.34.1 + Mathlib v4.34.1, zero sorrys.
-/

namespace GapCF

/-- Complete quotients of `α`: `α₀ = α`, `αₙ₊₁ = 1 / fract αₙ` (the Gauss map).
`α` is an explicit parameter (R53 fix: the `variable (α : ℝ)`-inclusion did not
fire for these pattern-matching definitions, so every definition takes `α`
explicitly and all recursive calls pass it). -/
noncomputable def cquot (α : ℝ) : ℕ → ℝ
  | 0 => α
  | n + 1 => (Int.fract (cquot α n))⁻¹

/-- Partial quotients: `aₙ = ⌊αₙ⌋`. -/
noncomputable def pquot (α : ℝ) (n : ℕ) : ℤ := ⌊cquot α n⌋

/-- Convergent numerators `pₙ`: `p₀ = a₀`, `p₁ = a₁a₀ + 1`, `pₙ₊₂ = aₙ₊₂pₙ₊₁ + pₙ`. -/
noncomputable def cnum (α : ℝ) : ℕ → ℤ
  | 0 => pquot α 0
  | 1 => pquot α 1 * pquot α 0 + 1
  | n + 2 => pquot α (n + 2) * cnum α (n + 1) + cnum α n

/-- Convergent denominators `qₙ`: `q₀ = 1`, `q₁ = a₁`, `qₙ₊₂ = aₙ₊₂qₙ₊₁ + qₙ`. -/
noncomputable def cden (α : ℝ) : ℕ → ℤ
  | 0 => 1
  | 1 => pquot α 1
  | n + 2 => pquot α (n + 2) * cden α (n + 1) + cden α n

/-- Real-valued partial quotients. -/
noncomputable def A (α : ℝ) (n : ℕ) : ℝ := (pquot α n : ℝ)

/-- Real-valued convergent numerators. -/
noncomputable def P (α : ℝ) (n : ℕ) : ℝ := (cnum α n : ℝ)

/-- Real-valued convergent denominators. -/
noncomputable def Q (α : ℝ) (n : ℕ) : ℝ := (cden α n : ℝ)

/-- Signed approximation error `eₙ = α qₙ − pₙ`; `δₙ = |eₙ|`. -/
noncomputable def cerr (α : ℝ) (n : ℕ) : ℝ := α * Q α n - P α n

variable {α : ℝ}

@[simp] theorem cquot_zero : cquot α 0 = α := rfl

@[simp] theorem cquot_succ (n : ℕ) : cquot α (n + 1) = (Int.fract (cquot α n))⁻¹ := rfl

theorem cnum_rec (n : ℕ) :
    cnum α (n + 2) = pquot α (n + 2) * cnum α (n + 1) + cnum α n := rfl

theorem cden_rec (n : ℕ) :
    cden α (n + 2) = pquot α (n + 2) * cden α (n + 1) + cden α n := rfl

theorem P_rec (n : ℕ) : P α (n + 2) = A α (n + 2) * P α (n + 1) + P α n := by
  simp only [P, A, cnum_rec, Int.cast_add, Int.cast_mul]

theorem Q_rec (n : ℕ) : Q α (n + 2) = A α (n + 2) * Q α (n + 1) + Q α n := by
  simp only [Q, A, cden_rec, Int.cast_add, Int.cast_mul]

/-- The fractional part of an irrational is irrational. -/
theorem irr_fract {x : ℝ} (h : Irrational x) : Irrational (Int.fract x) := by
  intro hq
  obtain ⟨q, hq⟩ := hq
  apply h
  refine ⟨(⌊x⌋ : ℚ) + q, ?_⟩
  push_cast
  rw [hq]
  exact Int.floor_add_fract x

/-- Every complete quotient of an irrational is irrational. -/
theorem cquot_irr (hirr : Irrational α) : ∀ n, Irrational (cquot α n) := by
  intro n
  induction n with
  | zero => simpa using hirr
  | succ n ih =>
    have h1 : Irrational (Int.fract (cquot α n)) := irr_fract ih
    have h2 : Irrational (Int.fract (cquot α n))⁻¹ := h1.inv
    simpa using h2

/-- `fract (cquot n) ≠ 0` for irrational `α` (the Gauss map never hits an integer). -/
theorem fract_cquot_ne_zero (hirr : Irrational α) (n : ℕ) :
    Int.fract (cquot α n) ≠ 0 := by
  intro h0
  have hirr_n := cquot_irr hirr n
  rw [Int.fract_eq_zero_iff] at h0
  obtain ⟨z, hz⟩ := h0
  apply hirr_n
  exact ⟨(z : ℚ), by exact_mod_cast hz⟩

/-- `0 < fract (cquot n)`. -/
theorem fract_cquot_pos (hirr : Irrational α) (n : ℕ) :
    0 < Int.fract (cquot α n) :=
  lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (fract_cquot_ne_zero hirr n))

/-- `cquot (n+1) > 0`. -/
theorem cquot_pos (hirr : Irrational α) (n : ℕ) : 0 < cquot α (n + 1) := by
  rw [cquot_succ]
  exact inv_pos.mpr (fract_cquot_pos hirr n)

/-- `cquot (n+1) > 1` (every complete quotient past the first exceeds 1). -/
theorem cquot_gt_one (hirr : Irrational α) (n : ℕ) : 1 < cquot α (n + 1) := by
  have hf := fract_cquot_pos hirr n
  have hf1 : Int.fract (cquot α n) < 1 := Int.fract_lt_one _
  rw [cquot_succ, inv_eq_one_div, lt_div_iff₀ hf, one_mul]
  exact hf1

/-- The key relation: `αₙ₊₁ * (αₙ − aₙ) = 1`. -/
theorem cquot_mul_fract (hirr : Irrational α) (n : ℕ) :
    cquot α (n + 1) * (cquot α n - A α n) = 1 := by
  have hfr : cquot α n - A α n = Int.fract (cquot α n) := by
    simp only [A, pquot]
    have := Int.floor_add_fract (cquot α n)
    linarith
  rw [hfr, cquot_succ]
  exact inv_mul_cancel₀ (fract_cquot_ne_zero hirr n)

/-- Partial quotients past the first are at least 1. -/
theorem pquot_ge_one (hirr : Irrational α) (n : ℕ) : 1 ≤ pquot α (n + 1) := by
  rw [pquot, Int.le_floor]
  have := cquot_gt_one hirr n
  simp only [cquot_succ] at this ⊢
  linarith [this]

/-- Convergent denominators are positive. -/
theorem cden_pos (hirr : Irrational α) : ∀ n, 0 < cden α n
  | 0 => by simp [cden]
  | 1 => by
    simp only [cden]
    have h := pquot_ge_one hirr 0
    rw [Nat.zero_add] at h
    omega
  | n + 2 => by
    have h1 := cden_pos hirr (n + 1)
    have h0 := cden_pos hirr n
    have ha := pquot_ge_one hirr (n + 1)
    have hmul : 1 ≤ pquot α (n + 2) * cden α (n + 1) := by
      have h1' : 1 ≤ cden α (n + 1) := h1
      calc (1 : ℤ) = 1 * 1 := by ring
        _ ≤ pquot α (n + 2) * cden α (n + 1) := by gcongr
    rw [cden_rec]
    omega

/-- Real-valued denominators are positive. -/
theorem Q_pos (hirr : Irrational α) (n : ℕ) : 0 < Q α n := by
  simp only [Q]
  exact_mod_cast cden_pos hirr n

/-! ## The error recurrence and determinant identity -/

theorem Q_zero : Q α 0 = 1 := by simp [Q, cden]

theorem P_zero : P α 0 = A α 0 := by simp [P, A, cnum]

theorem Q_one : Q α 1 = A α 1 := by simp [Q, A, cden]

theorem P_one : P α 1 = A α 1 * A α 0 + 1 := by
  simp only [P, A, cnum]
  push_cast
  ring

theorem cerr_zero_eq : cerr α 0 = α - A α 0 := by
  simp only [cerr, Q_zero, P_zero]
  ring

theorem cerr_one_eq : cerr α 1 = A α 1 * (α - A α 0) - 1 := by
  simp only [cerr, Q_one, P_one]
  ring

/-- Error recurrence: `eₙ₊₂ = aₙ₊₂ eₙ₊₁ + eₙ`. -/
theorem cerr_rec (n : ℕ) :
    cerr α (n + 2) = A α (n + 2) * cerr α (n + 1) + cerr α n := by
  simp only [cerr, P_rec, Q_rec]
  ring

/-- One step of the key error identity, with explicit indices
(kept separate so the main induction below needs no index massaging). -/
theorem cerr_step_aux (hirr : Irrational α) (m : ℕ)
    (ih : cquot α (m + 2) * cerr α (m + 1) = -cerr α m) :
    cquot α (m + 3) * cerr α (m + 2) = -cerr α (m + 1) := by
  have key : cquot α (m + 3) * (cquot α (m + 2) - A α (m + 2)) = 1 :=
    cquot_mul_fract hirr (m + 2)
  have h1 : cquot α (m + 2) - A α (m + 2) = (cquot α (m + 3))⁻¹ :=
    eq_inv_of_mul_eq_one_right key
  have hA : A α (m + 2) - cquot α (m + 2) = -(cquot α (m + 3))⁻¹ := by linarith
  have hcerr : cerr α m = -cquot α (m + 2) * cerr α (m + 1) := by
    linear_combination ih
  have h3 : cquot α (m + 3) * (A α (m + 2) * cerr α (m + 1) + cerr α m)
      = cerr α (m + 1) * (cquot α (m + 3) * (A α (m + 2) - cquot α (m + 2))) := by
    rw [hcerr]; ring
  have h4 : cquot α (m + 3) * (-(cquot α (m + 3))⁻¹) = -1 := by
    rw [mul_neg, mul_inv_cancel₀ (ne_of_gt (cquot_pos hirr (m + 2)))]
  calc cquot α (m + 3) * cerr α (m + 2)
      = cquot α (m + 3) * (A α (m + 2) * cerr α (m + 1) + cerr α m) := by
        rw [cerr_rec]
    _ = cerr α (m + 1) * (cquot α (m + 3) * (A α (m + 2) - cquot α (m + 2))) := h3
    _ = cerr α (m + 1) * (cquot α (m + 3) * (-(cquot α (m + 3))⁻¹)) := by rw [hA]
    _ = cerr α (m + 1) * -1 := by rw [h4]
    _ = -cerr α (m + 1) := by ring

/-- The key error identity: `αₙ₊₂ eₙ₊₁ = −eₙ` for all `n`. -/
theorem cerr_step (hirr : Irrational α) :
    ∀ n, cquot α (n + 2) * cerr α (n + 1) = -cerr α n := by
  intro n
  induction n with
  | zero =>
    show cquot α 2 * cerr α 1 = -cerr α 0
    have key : cquot α 2 * (cquot α 1 - A α 1) = 1 := cquot_mul_fract hirr 1
    have hc1 : cquot α 1 * (α - A α 0) = 1 := by
      have hfr : α - A α 0 = Int.fract α := by
        show α - (pquot α 0 : ℝ) = Int.fract α
        have h := Int.floor_add_fract α
        simp only [pquot, cquot_zero] at *
        linarith
      have hc1def : cquot α 1 = (Int.fract α)⁻¹ := rfl
      rw [hfr, hc1def]
      exact inv_mul_cancel₀ (fract_cquot_ne_zero hirr 0)
    have h1 : A α 1 * (α - A α 0) - 1
        = -(α - A α 0) * (cquot α 1 - A α 1) := by
      have hthis : (α - A α 0) * cquot α 1 = 1 := by rw [mul_comm]; exact hc1
      linear_combination hthis
    calc cquot α 2 * cerr α 1
        = cquot α 2 * (A α 1 * (α - A α 0) - 1) := by rw [cerr_one_eq]
      _ = cquot α 2 * (-(α - A α 0) * (cquot α 1 - A α 1)) := by rw [h1]
      _ = -(α - A α 0) * (cquot α 2 * (cquot α 1 - A α 1)) := by ring
      _ = -(α - A α 0) * 1 := by rw [key]
      _ = -(α - A α 0) := by ring
      _ = -cerr α 0 := by rw [cerr_zero_eq]
  | succ n ih => exact cerr_step_aux hirr n ih

/-- Determinant identity, one step. -/
theorem cerr_det_aux (m : ℕ)
    (ih : cerr α m * Q α (m + 1) - cerr α (m + 1) * Q α m = (-1 : ℝ) ^ m) :
    cerr α (m + 1) * Q α (m + 2) - cerr α (m + 2) * Q α (m + 1)
      = (-1 : ℝ) ^ (m + 1) := by
  have h1 : Q α (m + 2) = A α (m + 2) * Q α (m + 1) + Q α m := Q_rec m
  have h2 : cerr α (m + 2) = A α (m + 2) * cerr α (m + 1) + cerr α m := cerr_rec m
  rw [h1, h2, pow_succ]
  linear_combination -ih

/-- Determinant identity: `eₙ qₙ₊₁ − eₙ₊₁ qₙ = (−1)ⁿ`. -/
theorem cerr_det :
    ∀ n, cerr α n * Q α (n + 1) - cerr α (n + 1) * Q α n = (-1 : ℝ) ^ n := by
  intro n
  induction n with
  | zero =>
    show cerr α 0 * Q α 1 - cerr α 1 * Q α 0 = (-1 : ℝ) ^ 0
    rw [cerr_zero_eq, cerr_one_eq, Q_zero, Q_one, pow_zero]
    ring
  | succ n ih => exact cerr_det_aux n ih

/-! ## The error formula and the ratio identity (C24 Lemma 1) -/

/-- C24 Lemma 1, first part: `|eₙ₊₁| = 1 / (αₙ₊₂ qₙ₊₁ + qₙ)`. -/
theorem cf_error_formula (hirr : Irrational α) (n : ℕ) :
    |cerr α (n + 1)| = 1 / (cquot α (n + 2) * Q α (n + 1) + Q α n) := by
  have hdet := cerr_det (α := α) n
  have hstep := cerr_step hirr n
  have hpos : 0 < cquot α (n + 2) * Q α (n + 1) + Q α n :=
    add_pos (mul_pos (cquot_pos hirr (n + 1)) (Q_pos hirr (n + 1))) (Q_pos hirr n)
  have hmul : cerr α (n + 1) * (cquot α (n + 2) * Q α (n + 1) + Q α n)
      = -(-1 : ℝ) ^ n := by
    linear_combination -hdet + (Q α (n + 1)) * hstep
  have habs : |cerr α (n + 1)| * (cquot α (n + 2) * Q α (n + 1) + Q α n) = 1 := by
    have h1 : |(-(-1 : ℝ) ^ n)| = 1 := by
      rw [abs_neg, abs_pow, abs_neg, abs_one, one_pow]
    have h2 : |cerr α (n + 1) * (cquot α (n + 2) * Q α (n + 1) + Q α n)| = 1 := by
      rw [hmul]; exact h1
    rw [abs_mul, abs_of_pos hpos] at h2
    exact h2
  rw [eq_div_iff (ne_of_gt hpos)]
  exact habs

/-- Error at index 0: `|e₀| = 1 / α₁`. -/
theorem cf_error_zero (hirr : Irrational α) : |cerr α 0| = 1 / cquot α 1 := by
  have h0 : cerr α 0 = Int.fract α := by
    rw [cerr_zero_eq]
    show α - (pquot α 0 : ℝ) = Int.fract α
    have h := Int.floor_add_fract α
    simp only [pquot, cquot_zero] at *
    linarith
  have hf : 0 < Int.fract α := fract_cquot_pos hirr 0
  have hc1 : cquot α 1 = (Int.fract α)⁻¹ := rfl
  rw [h0, abs_of_pos hf, hc1, one_div, inv_inv]

/-- Every error is nonzero. -/
theorem cerr_abs_pos (hirr : Irrational α) : ∀ n, 0 < |cerr α n|
  | 0 => by rw [cf_error_zero hirr]; exact one_div_pos.mpr (cquot_pos hirr 0)
  | n + 1 => by
    rw [cf_error_formula hirr n]
    exact one_div_pos.mpr
      (add_pos (mul_pos (cquot_pos hirr (n + 1)) (Q_pos hirr (n + 1))) (Q_pos hirr n))

/-- Algebraic core of the ratio:
`αₙ₊₃ (αₙ₊₂ qₙ₊₁ + qₙ) = αₙ₊₃ qₙ₊₂ + qₙ₊₁`. -/
theorem cf_ratio_alg (hirr : Irrational α) (m : ℕ) :
    cquot α (m + 3) * (cquot α (m + 2) * Q α (m + 1) + Q α m)
      = cquot α (m + 3) * Q α (m + 2) + Q α (m + 1) := by
  have hQ : Q α (m + 2) = A α (m + 2) * Q α (m + 1) + Q α m := Q_rec m
  have hA : cquot α (m + 2) = A α (m + 2) + (cquot α (m + 3))⁻¹ := by
    have h2 : cquot α (m + 2) - A α (m + 2) = (cquot α (m + 3))⁻¹ :=
      eq_inv_of_mul_eq_one_right (cquot_mul_fract hirr (m + 2))
    linarith
  have hc : cquot α (m + 3) * (cquot α (m + 3))⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt (cquot_pos hirr (m + 2)))
  rw [hA, hQ]
  linear_combination (Q α (m + 1)) * hc

/-- C24 Lemma 1, the ratio identity: `|eₙ₊₁| / |eₙ| = 1 / αₙ₊₂`. -/
theorem cf_ratio_formula (hirr : Irrational α) (n : ℕ) :
    |cerr α (n + 1)| / |cerr α n| = 1 / cquot α (n + 2) := by
  cases n with
  | zero =>
    show |cerr α 1| / |cerr α 0| = 1 / cquot α 2
    have e1 : |cerr α 1| = 1 / (cquot α 2 * Q α 1 + Q α 0) := cf_error_formula hirr 0
    have e0 : |cerr α 0| = 1 / cquot α 1 := cf_error_zero hirr
    have hD : (0:ℝ) < cquot α 2 * Q α 1 + Q α 0 :=
      add_pos (mul_pos (cquot_pos hirr 1) (Q_pos hirr 1)) (Q_pos hirr 0)
    have hc2 : (0:ℝ) < cquot α 2 := cquot_pos hirr 1
    have hmul : cquot α 1 * cquot α 2 = cquot α 2 * Q α 1 + Q α 0 := by
      have key : cquot α 2 * (cquot α 1 - A α 1) = 1 := cquot_mul_fract hirr 1
      rw [Q_one, Q_zero]
      linear_combination key
    have h1 : (1 / (cquot α 2 * Q α 1 + Q α 0)) / (1 / cquot α 1)
        = (cquot α 1) / (cquot α 2 * Q α 1 + Q α 0) := by
      rw [div_eq_mul_inv, one_div, one_div, inv_inv, div_eq_mul_inv, mul_comm]
    rw [e1, e0, h1, div_eq_div_iff (ne_of_gt hD) (ne_of_gt hc2)]
    linear_combination hmul
  | succ n =>
    show |cerr α (n + 2)| / |cerr α (n + 1)| = 1 / cquot α (n + 3)
    have e1 : |cerr α (n + 2)|
        = 1 / (cquot α (n + 3) * Q α (n + 2) + Q α (n + 1)) :=
      cf_error_formula hirr (n + 1)
    have e0 : |cerr α (n + 1)|
        = 1 / (cquot α (n + 2) * Q α (n + 1) + Q α n) :=
      cf_error_formula hirr n
    have hD : (0:ℝ) < cquot α (n + 2) * Q α (n + 1) + Q α n :=
      add_pos (mul_pos (cquot_pos hirr (n + 1)) (Q_pos hirr (n + 1))) (Q_pos hirr n)
    have hD' : (0:ℝ) < cquot α (n + 3) * Q α (n + 2) + Q α (n + 1) :=
      add_pos (mul_pos (cquot_pos hirr (n + 2)) (Q_pos hirr (n + 2))) (Q_pos hirr (n + 1))
    have hc3 : (0:ℝ) < cquot α (n + 3) := cquot_pos hirr (n + 2)
    have h1 : (1 / (cquot α (n + 3) * Q α (n + 2) + Q α (n + 1)))
          / (1 / (cquot α (n + 2) * Q α (n + 1) + Q α n))
        = (cquot α (n + 2) * Q α (n + 1) + Q α n)
          / (cquot α (n + 3) * Q α (n + 2) + Q α (n + 1)) := by
      rw [div_eq_mul_inv, one_div, one_div, inv_inv, div_eq_mul_inv, mul_comm]
    rw [e1, e0, h1, div_eq_div_iff (ne_of_gt hD') (ne_of_gt hc3)]
    linear_combination cf_ratio_alg hirr n

/-! ## Sign alternation and the (F1) determinant identity -/

/-- Sign alternation: `(−1)ⁿ eₙ > 0`. -/
theorem cerr_sign (hirr : Irrational α) : ∀ n, 0 < (-1 : ℝ) ^ n * cerr α n := by
  intro n
  induction n with
  | zero =>
    show 0 < (-1 : ℝ) ^ 0 * cerr α 0
    rw [pow_zero, one_mul, cerr_zero_eq]
    show 0 < α - A α 0
    have h := fract_cquot_pos hirr 0
    show 0 < α - (pquot α 0 : ℝ)
    have h2 := Int.floor_add_fract α
    simp only [pquot, cquot_zero] at *
    linarith
  | succ n ih =>
    have hstep := cerr_step hirr n
    have hc : cquot α (n + 2) ≠ 0 := ne_of_gt (cquot_pos hirr (n + 1))
    have hcerr : cerr α (n + 1) = -cerr α n / cquot α (n + 2) := by
      rw [eq_div_iff hc]
      linear_combination hstep
    have hcalc : (-1 : ℝ) ^ (n + 1) * cerr α (n + 1)
        = ((-1 : ℝ) ^ n * cerr α n) / cquot α (n + 2) := by
      rw [pow_succ, hcerr]
      ring
    rw [hcalc]
    exact div_pos ih (cquot_pos hirr (n + 1))

/-- The `(F1)` identity for the C22/C23/C25 assembly: for even `m`,
`qₘ₊₁ δₘ + qₘ δₘ₊₁ = 1` where `δₖ = |eₖ|`. -/
theorem cf_det_identity (hirr : Irrational α) (m : ℕ) (hm : Even m) :
    Q α (m + 1) * |cerr α m| + Q α m * |cerr α (m + 1)| = 1 := by
  have hdet := cerr_det (α := α) m
  have e1 : (-1 : ℝ) ^ m = 1 := hm.neg_one_pow
  rw [e1] at hdet
  have hcm : 0 < cerr α m := by
    have h := cerr_sign hirr m
    rwa [e1, one_mul] at h
  have e2 : (-1 : ℝ) ^ (m + 1) = -1 := by rw [pow_succ, e1, one_mul]
  have hcm1 : cerr α (m + 1) < 0 := by
    have h := cerr_sign hirr (m + 1)
    rw [e2, neg_one_mul] at h
    linarith
  rw [abs_of_pos hcm, abs_of_neg hcm1]
  linear_combination hdet

end GapCF
