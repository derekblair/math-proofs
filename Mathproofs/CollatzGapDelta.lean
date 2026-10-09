import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Δ-sign machinery for the Collatz gap-factor argmin theorems (C22 / C23 / C25 / C26)

Source proofs: `~/workspace/math-unsolved/c22_proofs_r24.md`,
`~/workspace/math-unsolved/c23_proofs_r27.md`,
`~/workspace/math-unsolved/c25_proofs_r33.md`,
`~/workspace/math-unsolved/c26_proofs_r36.md`
(Round 41 of the continuous math-solving program, Lean formalization batch).

These are the *structural* (non-analytic) components of the C22–C26 batch,
stated and proved here in fully self-contained form, independent of the
Collatz / continued-fraction machinery. The analytic inputs
(`gap_sinh_superlinear`, `gap_sinh_le_mul_exp`, `gap_log_one_add_ge`)
were machine-checked in Round 37 (`Mathproofs.CollatzGapSinh`).

Variable dictionary (for wiring to the CF context later):
- `Q` = Q_{t+1} (the middle denominator), `q` = q' = q_{n-1},
- `v` = x(t+1) (the gap exponent), `d` = δ' = δ_{n-1} (the step),
- the hypothesis `d < v` is `x(t+1) > δ'`, i.e. `x(t+1) ≥ x(a-1) = δ'+δₙ > δ'`.

Contents:
- `gap_delta_sign_criterion` — C22 Lemma 1 (the linchpin): the exact
  Δ-sign criterion, `Δ(t) < 0 ↔ (q'/Q)·sinh(x(t+1)·ln2/2) > sinh(δ'·ln2/2)`,
  as a pure real-analysis identity. Used by C22 Thm 2/3, C23(a), C25 Thm 1,
  and (via the margin form) C26.
- `gap_sinh_product_identity` — C26 Lemma D1:
  `S(λ+1)·S(λ−1) = S(λ)² − 1` for `S(λ) = sinh(λz)/sinh(z)`.
- `gap_cf_selector_identity` — algebraic core of the C24 identity
  `ρ = 1/α_{n+1}`: given the classical CF error formula
  `δₖ = 1/(α_{k+1}·qₖ + q_{k-1})` (taken as the definitions here),
  `δₙ/δ_{n-1} = 1/α_{n+1}` by pure algebra. The error formula itself
  (from Mathlib's continued-fraction machinery) is not yet formalized.
- `gap_argmin_of_delta_signs` — the argmin-selection algebra:
  if `g` strictly decreases on `{1,…,m}` and strictly increases on
  `{m,…,N}`, then `m` is the unique argmin on `{1,…,N}`.

Checked with Lean 4.34.1 + Mathlib v4.34.1, zero sorrys.
Remaining for the full batch: Δ strict monotonicity (C18b — needs
`HasDerivAt` plumbing for `S″(u) = (ln2)²(ψ(2^{u−δ′}) − ψ(2^u))` via
ψ decreasing; the hand proof's algebra was verified symbolically),
the C24 error formula from Mathlib CF theory, and wiring these
self-contained lemmas to the CF definitions (`G`, `Q_t`, `x(t)`).
-/

/-- Exact Δ-sign criterion (C22 Lemma 1, self-contained form).

With `Q = Q_{t+1} > q' = q > 0`, `v = x(t+1) > δ' = d > 0`:
`Δ(t) < 0` (i.e. `ln(Q-part) + ln(S-part) < 0`) holds iff
`(q'/Q)·sinh(x(t+1)·ln2/2) > sinh(δ'·ln2/2)`.

Proof (following the hand proof in `c22_proofs_r24.md`):
write `w = 2^v`, `c = cosh(δ'·ln2)`, `D = (2^{v+d}−1)(2^{v−d}−1)`.
The Q-part is `ln(1 − (q/Q)²)` since `Q_{t+2}·Q_t − Q_{t+1}² = −q²`;
the S-part denominator factors as `D = w² − 2wc + 1`.
`Δ(t) < 0` unfolds to `(w−1)²(Q²−q²) < Q²·D`, i.e.
`2Q²w(c−1) < q²(w−1)²`; with `c − 1 = 2sinh²(δ'ln2/2)` and square
roots, `(w−1)/(2√w) = sinh(v·ln2/2)` closes the chain. -/
theorem gap_delta_sign_criterion
    (Q q v d : ℝ) (hq : 0 < q) (hQ : q < Q) (hd : 0 < d) (hv : d < v) :
    Real.log (1 - (q / Q) ^ 2) +
      Real.log (((2:ℝ) ^ v - 1) ^ 2 /
        (((2:ℝ) ^ (v + d) - 1) * ((2:ℝ) ^ (v - d) - 1))) < 0
    ↔ Real.sinh (d * Real.log 2 / 2) < (q / Q) * Real.sinh (v * Real.log 2 / 2) := by
  have hQpos : (0:ℝ) < Q := lt_trans hq hQ
  have hQne : Q ≠ 0 := ne_of_gt hQpos
  have hv0 : (0:ℝ) < v := lt_trans hd hv
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set w : ℝ := (2:ℝ) ^ v with hw_def
  set e : ℝ := (2:ℝ) ^ d with he_def
  set u : ℝ := d * Real.log 2 with hu_def
  have hw1 : (1:ℝ) < w := by
    rw [hw_def]
    calc (1:ℝ) = (2:ℝ) ^ 0 := by rw [Real.rpow_zero]
      _ < (2:ℝ) ^ v := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hv0
  have he1 : (1:ℝ) < e := by
    rw [he_def]
    calc (1:ℝ) = (2:ℝ) ^ 0 := by rw [Real.rpow_zero]
      _ < (2:ℝ) ^ d := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hd
  have hwpos : (0:ℝ) < w := by linarith
  have hsplit1 : (2:ℝ) ^ (v + d) = w * e := by
    rw [hw_def, he_def]
    exact Real.rpow_add (by norm_num) v d
  have hsplit2 : (2:ℝ) ^ (v - d) = w / e := by
    rw [hw_def, he_def]
    exact Real.rpow_sub (by norm_num) v d
  have he_exp : e = Real.exp u := by
    rw [he_def, hu_def, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) d]
    congr 1
    ring
  -- The S-part denominator factors as w² − 2w·cosh(u) + 1.
  have hD : ((2:ℝ) ^ (v + d) - 1) * ((2:ℝ) ^ (v - d) - 1)
      = w ^ 2 - 2 * w * Real.cosh u + 1 := by
    have hdiv : w / Real.exp u = w * Real.exp (-u) := by
      rw [div_eq_mul_inv, Real.exp_neg]
    have hexp_inv : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hexpand : (w * Real.exp u - 1) * (w * Real.exp (-u) - 1)
        = w ^ 2 * (Real.exp u * Real.exp (-u))
          - w * (Real.exp u + Real.exp (-u)) + 1 := by ring
    rw [hsplit1, hsplit2, he_exp, Real.cosh_eq, hdiv, hexpand, hexp_inv]
    ring
  have hD1 : (0:ℝ) < (2:ℝ) ^ (v + d) - 1 := by
    have h : (1:ℝ) < (2:ℝ) ^ (v + d) :=
      calc (1:ℝ) = (2:ℝ) ^ 0 := by rw [Real.rpow_zero]
        _ < (2:ℝ) ^ (v + d) :=
            Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    linarith
  have hD2 : (0:ℝ) < (2:ℝ) ^ (v - d) - 1 := by
    have h : (1:ℝ) < (2:ℝ) ^ (v - d) :=
      calc (1:ℝ) = (2:ℝ) ^ 0 := by rw [Real.rpow_zero]
        _ < (2:ℝ) ^ (v - d) :=
            Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    linarith
  have hDpos : (0:ℝ) < w ^ 2 - 2 * w * Real.cosh u + 1 := by
    rw [← hD]; exact mul_pos hD1 hD2
  have hDne : w ^ 2 - 2 * w * Real.cosh u + 1 ≠ 0 := ne_of_gt hDpos
  -- The Q-part `1 − (q/Q)²` is positive since `q < Q`.
  have hA : (0:ℝ) < 1 - (q / Q) ^ 2 := by
    have hqq : (q / Q) ^ 2 < 1 := by
      rw [div_pow, div_lt_one₀ (by positivity : (0:ℝ) < Q ^ 2)]
      have hprod : (0:ℝ) < (Q - q) * (Q + q) :=
        mul_pos (sub_pos.mpr hQ) (by linarith)
      nlinarith [hprod]
    linarith
  have hB : (0:ℝ) < (w - 1) ^ 2 /
      (((2:ℝ) ^ (v + d) - 1) * ((2:ℝ) ^ (v - d) - 1)) := by
    apply div_pos _ (mul_pos hD1 hD2)
    exact pow_pos (by linarith : (0:ℝ) < w - 1) 2
  -- Combine the two logs; `log X < 0 ↔ X < 1`.
  rw [← Real.log_mul (ne_of_gt hA) (ne_of_gt hB),
    Real.log_neg_iff (mul_pos hA hB), hD]
  -- Step 1: cross-multiply: `A·B < 1 ↔ (Q²−q²)(w−1)² < Q²·D'`.
  have hstep1 : (1 - (q / Q) ^ 2) * ((w - 1) ^ 2 / (w ^ 2 - 2 * w * Real.cosh u + 1)) < 1
      ↔ (Q ^ 2 - q ^ 2) * (w - 1) ^ 2
        < Q ^ 2 * (w ^ 2 - 2 * w * Real.cosh u + 1) := by
    have h1 : (1:ℝ) - (q / Q) ^ 2 = (Q ^ 2 - q ^ 2) / Q ^ 2 := by
      field_simp
    rw [h1, div_mul_div_comm,
      div_lt_one₀ (by positivity : (0:ℝ) < Q ^ 2 * (w ^ 2 - 2 * w * Real.cosh u + 1))]
  -- Step 2: `(Q²−q²)(w−1)² < Q²·D' ↔ 2Q²w(cosh u − 1) < q²(w−1)²`.
  have hstep2 : (Q ^ 2 - q ^ 2) * (w - 1) ^ 2
        < Q ^ 2 * (w ^ 2 - 2 * w * Real.cosh u + 1)
      ↔ 2 * Q ^ 2 * w * (Real.cosh u - 1) < q ^ 2 * (w - 1) ^ 2 := by
    have heq : (Q ^ 2 - q ^ 2) * (w - 1) ^ 2
          - Q ^ 2 * (w ^ 2 - 2 * w * Real.cosh u + 1)
        = 2 * Q ^ 2 * w * (Real.cosh u - 1) - q ^ 2 * (w - 1) ^ 2 := by ring
    constructor <;> intro h <;> linarith
  -- `cosh u − 1 = 2·sinh²(u/2)`.
  have hcosh1 : Real.cosh u - 1 = 2 * Real.sinh (u / 2) ^ 2 := by
    have h2u : (2:ℝ) * (u / 2) = u := by ring
    have h1 : Real.cosh u = 2 * Real.cosh (u / 2) ^ 2 - 1 := by
      conv_lhs => rw [← h2u, Real.cosh_two_mul]
      rw [Real.sinh_sq]
      ring
    have hs := Real.sinh_sq (u / 2)
    linarith
  -- Step 3: take square roots (both sides nonneg).
  have hsu : (0:ℝ) < Real.sinh (u / 2) :=
    Real.sinh_pos_iff.mpr (by rw [hu_def]; positivity)
  have hnn1 : (0:ℝ) ≤ 2 * Q * Real.sqrt w * Real.sinh (u / 2) := by positivity
  have hnn2 : (0:ℝ) ≤ q * (w - 1) := by
    have hw1' : (0:ℝ) < w - 1 := by linarith
    positivity
  have e1 : (2 * Q * Real.sqrt w * Real.sinh (u / 2)) ^ 2
      = 2 * Q ^ 2 * w * (2 * Real.sinh (u / 2) ^ 2) := by
    simp only [mul_pow, Real.sq_sqrt (le_of_lt hwpos)]
    ring
  have e2 : (q * (w - 1)) ^ 2 = q ^ 2 * (w - 1) ^ 2 := by ring
  have hstep3 : 2 * Q ^ 2 * w * (Real.cosh u - 1) < q ^ 2 * (w - 1) ^ 2
      ↔ 2 * Q * Real.sqrt w * Real.sinh (u / 2) < q * (w - 1) := by
    rw [hcosh1, ← e1, ← e2, sq_lt_sq, abs_of_nonneg hnn1, abs_of_nonneg hnn2]
  -- The key sinh identity: `(w−1)/(2√w) = sinh(v·ln2/2)`.
  have hsinh_id : (w - 1) / (2 * Real.sqrt w) = Real.sinh (v * Real.log 2 / 2) := by
    have hwexp : w = Real.exp (v * Real.log 2) := by
      rw [hw_def, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) v]
      congr 1
      ring
    have hsq : Real.sqrt w = Real.exp (v * Real.log 2 / 2) := by
      rw [hwexp, ← Real.exp_half]
    have hexp2 : Real.exp (v * Real.log 2) = (Real.exp (v * Real.log 2 / 2)) ^ 2 := by
      have hvv : v * Real.log 2 = v * Real.log 2 / 2 + v * Real.log 2 / 2 := by ring
      conv_lhs => rw [hvv]
      rw [Real.exp_add, pow_two]
    have hE : Real.exp (v * Real.log 2 / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have hexp_neg : Real.exp (-(v * Real.log 2 / 2))
        = (Real.exp (v * Real.log 2 / 2))⁻¹ := Real.exp_neg _
    rw [hsq, hwexp, Real.sinh_eq, hexp2, hexp_neg]
    field_simp
  -- Step 4: divide by `2Q√w > 0`.
  have hstep4 : 2 * Q * Real.sqrt w * Real.sinh (u / 2) < q * (w - 1)
      ↔ Real.sinh (u / 2) < (q / Q) * Real.sinh (v * Real.log 2 / 2) := by
    rw [← hsinh_id]
    have hrhs : (q / Q) * ((w - 1) / (2 * Real.sqrt w))
        = (q * (w - 1)) / (Q * (2 * Real.sqrt w)) := div_mul_div_comm _ _ _ _
    have hpos : (0:ℝ) < Q * (2 * Real.sqrt w) := by positivity
    rw [hrhs, lt_div_iff₀ hpos]
    have key : 2 * Q * Real.sqrt w * Real.sinh (u / 2)
        = Real.sinh (u / 2) * (Q * (2 * Real.sqrt w)) := by ring
    rw [key]
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

/-- Sub-lemma D1 (C26 Lemma D1): the sinh product identity.

For `S(λ) = sinh(λz)/sinh(z)` (with `sinh z ≠ 0`):
`S(λ+1)·S(λ−1) = S(λ)² − 1`.
Proof: `sinh((λ±1)z) = sinh(λz)cosh(z) ± cosh(λz)sinh(z)`, so the product
is `sinh²(λz)cosh²(z) − cosh²(λz)sinh²(z) = sinh²(λz) − sinh²(z)`
(using `cosh² = 1 + sinh²` twice); divide by `sinh²(z)`. -/
theorem gap_sinh_product_identity (z lam : ℝ) (hz : Real.sinh z ≠ 0) :
    (Real.sinh ((lam + 1) * z) / Real.sinh z)
        * (Real.sinh ((lam - 1) * z) / Real.sinh z)
      = (Real.sinh (lam * z) / Real.sinh z) ^ 2 - 1 := by
  have e1 : Real.sinh ((lam + 1) * z)
      = Real.sinh (lam * z) * Real.cosh z + Real.cosh (lam * z) * Real.sinh z := by
    have h : (lam + 1) * z = lam * z + z := by ring
    rw [h, Real.sinh_add]
  have e2 : Real.sinh ((lam - 1) * z)
      = Real.sinh (lam * z) * Real.cosh z - Real.cosh (lam * z) * Real.sinh z := by
    have h : (lam - 1) * z = lam * z - z := by ring
    rw [h, Real.sinh_sub]
  have key : Real.sinh ((lam + 1) * z) * Real.sinh ((lam - 1) * z)
      = Real.sinh (lam * z) ^ 2 - Real.sinh z ^ 2 := by
    rw [e1, e2]
    have h1 : Real.cosh (lam * z) ^ 2 = 1 + Real.sinh (lam * z) ^ 2 := by
      have hs := Real.sinh_sq (lam * z); linarith
    have h2 : Real.cosh z ^ 2 = 1 + Real.sinh z ^ 2 := by
      have hs := Real.sinh_sq z; linarith
    linear_combination Real.sinh (lam * z) ^ 2 * h2 - Real.sinh z ^ 2 * h1
  rw [div_mul_div_comm, key, div_pow, pow_two (Real.sinh z), sub_div,
    div_self (mul_ne_zero hz hz)]

/-- Algebraic core of the C24 tail-selector identity `ρ = 1/α_{n+1}`.

Given the classical continued-fraction error formula
`δₖ = 1/(α_{k+1}·qₖ + q_{k-1})` (taken here as the *definitions* of the
two `δ` quantities), the complete-quotient relation `αₙ = aₙ + 1/α_{n+1}`
and the denominator recurrence `qₙ = aₙ·q_{n-1} + q_{n-2}`, the ratio
`δₙ/δ_{n-1}` equals `1/α_{n+1}` by pure algebra. The error formula itself
(from Mathlib's continued-fraction theory) is not yet formalized. -/
theorem gap_cf_selector_identity (a_n α_np1 q_n q_nm1 q_nm2 : ℝ)
    (hα : 0 < α_np1) (ha : 1 ≤ a_n) (hq1 : 0 < q_nm1) (hq2 : 0 < q_nm2)
    (hqn : q_n = a_n * q_nm1 + q_nm2) :
    (1 / (α_np1 * q_n + q_nm1)) / (1 / ((a_n + 1 / α_np1) * q_nm1 + q_nm2))
      = 1 / α_np1 := by
  have hαne : α_np1 ≠ 0 := ne_of_gt hα
  have ha0 : (0:ℝ) < a_n := by linarith
  have hqn_pos : (0:ℝ) < q_n := by
    rw [hqn]
    have h := mul_pos ha0 hq1
    linarith
  have hXne : α_np1 * q_n + q_nm1 ≠ 0 := by positivity
  have key : (a_n + 1 / α_np1) * q_nm1 + q_nm2
      = (α_np1 * q_n + q_nm1) / α_np1 := by
    rw [hqn]
    field_simp
    ring
  rw [key]
  field_simp

/-- Argmin-selection algebra (C22/C23/C25): from `Δ` signs to `t*`.

If `g` is strictly decreasing on `{1, …, m}` (i.e. `g(t+1) < g(t)` for
`1 ≤ t`, `t+1 ≤ m`) and strictly increasing on `{m, …, N}` (i.e.
`g(t) < g(t+1)` for `m ≤ t`, `t+1 ≤ N`), then `m` is the unique minimizer
of `g` on `{1, …, N}`: `g m < g t` for every `t ∈ {1,…,N}`, `t ≠ m`.

In the applications, `g = G` (or `ln G`), the decrease/increase comes
from the Δ-sign criterion (`gap_delta_sign_criterion`) plus Δ strict
monotonicity (C18b), e.g. C22: `Δ(m−1) < 0 < Δ(m)` gives `t* = m`. -/
theorem gap_argmin_of_delta_signs (g : ℕ → ℝ) (m N : ℕ)
    (hdec : ∀ t, 1 ≤ t → t + 1 ≤ m → g (t + 1) < g t)
    (hinc : ∀ t, m ≤ t → t + 1 ≤ N → g t < g (t + 1)) :
    ∀ t, 1 ≤ t → t ≤ N → t ≠ m → g m < g t := by
  intro t ht1 htN htm
  rcases lt_or_gt_of_ne htm with h | h
  · -- `t < m`: chain `g m ≤ g (t+1) < g t` via a descending induction.
    have aux : ∀ j, j ≤ m - t → g m ≤ g (m - j) := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        have hle := ih (by omega)
        have hmj1 : m - (j + 1) + 1 = m - j := by omega
        have h1 : 1 ≤ m - (j + 1) := by omega
        have h2 : m - (j + 1) + 1 ≤ m := by omega
        have hdec' := hdec (m - (j + 1)) h1 h2
        rw [hmj1] at hdec'
        linarith
    have hle1 := aux (m - t) le_rfl
    have hmt : m - (m - t) = t := by omega
    rw [hmt] at hle1
    have hdec_t := hdec t ht1 (by omega)
    have hle2 := aux (m - t - 1) (by omega)
    have hmt2 : m - (m - t - 1) = t + 1 := by omega
    rw [hmt2] at hle2
    linarith
  · -- `m < t`: chain `g m ≤ g (t−1) < g t` via an ascending induction.
    have aux : ∀ j, j ≤ t - m → g m ≤ g (m + j) := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        have hle := ih (by omega)
        have hmj1 : m + (j + 1) = (m + j) + 1 := by ring
        have hinc' := hinc (m + j) (by omega) (by omega)
        rw [hmj1]
        linarith
    have hle1 := aux (t - m) le_rfl
    have htm1 : m + (t - m) = t := by omega
    rw [htm1] at hle1
    have hinc_t := hinc (t - 1) (by omega) (by omega)
    have htm3 : (t - 1) + 1 = t := by omega
    rw [htm3] at hinc_t
    have hle2 := aux (t - m - 1) (by omega)
    have htm2 : m + (t - m - 1) = t - 1 := by omega
    rw [htm2] at hle2
    linarith
