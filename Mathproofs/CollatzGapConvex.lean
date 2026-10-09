import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathproofs.CollatzGapDelta

/-!
# C18b (Δ strict monotonicity) and C26 margin duality, discrete/exact form

Source proofs: `~/workspace/math-unsolved/ROUND18_DOSSIER.md` (C18b),
`~/workspace/math-unsolved/c26_proofs_r36.md` (C26/C27),
`~/workspace/math-unsolved/c22_proofs_r24.md` (Lemma 1 / criterion).
(Round 45 of the continuous math-solving program, Lean formalization lane.)

The hand proof of C18b goes through continuous second derivatives
(`S″(u) = (ln2)²·(ψ(2^{u−δ′}) − ψ(2^u))` via `HasDerivAt` plumbing).
Here we take a **strictly stronger and calculus-free route**: the discrete
second differences of both parts of `ln G` are positive by *pure polynomial
identities* —
- T-part: `A³(A+2c) − (A+c)³(A−c) = c³(2A+c) > 0`,
- S-part: `(X−c)³(Xc−1) − c(X−c²)(X−1)³ = (c−1)³·X·(X²−c) > 0`,
verified numerically in `/tmp` (50-digit) and by `ring` below.
Since the hand proofs consume C18b only as "`Δ(t) = ln G(t+1) − ln G(t)`
is strictly increasing" (fact (F2) in `c22_proofs_r24.md`,
`c23_proofs_r27.md`, `c25_proofs_r33.md`, `c26_proofs_r36.md`), the
discrete statement is exactly what the batch needs — no `HasDerivAt`
plumbing, no ψ.

Variable dictionary (CF wiring):
- `qp = q′ = q_{n-1}`, `qpp = q″ = q_{n-2}`, `d = δ′ = δ_{n-1}`, `dn = δ_n`,
- `gapQ qp qpp t = t·qp + qpp = Q_t` (semiconvergent denominators),
- `gapx a d dn t = (a−t)·d + dn = x(t)` (gap exponent),
- `gapT qp qpp t = ln(1 + qp/(t·qp+qpp)) = ln(Q_{t+1}/Q_t)`,
- `gapS d u = ln((2^u−1)/(2^{u−d}−1))`, so `ln G(t) = gapT(t) + gapS(gapu(t))`,
- `gapDelta` = first differences of `ln G`.

Contents:
- `gapT_seconddiff_pos`, `gapS_seconddiff_pos` — the two second-difference
  lemmas (C18b halves).
- `gapDelta_strictly_increasing` — **C18b proper**: `Δ(t)` strictly
  increasing on the block interior.
- `gapQ_det` — the Q-determinant `Q_{t+2}·Q_t − Q_{t+1}² = −q′²`
  (C26 Lemma D2; also C22 Lemma 1's Q-part).
- `gap_criterion_CF` — the exact Δ-sign criterion
  (`gap_delta_sign_criterion`) instantiated in CF variables.
- `gap_delta_sign_criterion_eq` — the equality case `Δlog = 0 ↔ A = B`
  of the criterion (needed for the full C26 trichotomy).
- `gap_margin_chain` — the C26 margin algebra:
  `M⁻ ⋚ M⁺ ↔ M0 ⋚ 1` via D1 (`gap_sinh_product_identity`) + D2.
- `gap_margin_duality` — **C26 proper**: margin order ↔ Δ-sign,
  via the chain + the margin bridge + the criterion trichotomy.

Checked with Lean 4.34.1 + Mathlib v4.34.1, zero sorrys.
-/

open Real

/-- The T-part of `ln G`: `T(t) = ln(1 + q′/(t·q′+q″)) = ln(Q_{t+1}/Q_t)`. -/
noncomputable def gapT (qp qpp : ℝ) (t : ℝ) : ℝ :=
  Real.log (1 + qp / (t * qp + qpp))

/-- The S-part of `ln G`: `S(u) = ln((2^u−1)/(2^{u−d}−1))`. -/
noncomputable def gapS (d : ℝ) (u : ℝ) : ℝ :=
  Real.log (((2:ℝ)^u - 1) / ((2:ℝ)^(u-d) - 1))

/-- The linear gap-exponent schedule: `u(t) = (a−t)·δ′ + δ_n`. -/
noncomputable def gapu (a d e : ℝ) (t : ℝ) : ℝ := (a - t) * d + e

/-- First differences of `ln G(t) = T(t) + S(u(t))`: `Δ(t) = lnG(t+1) − lnG(t)`. -/
noncomputable def gapDelta (qp qpp a d e : ℝ) (t : ℝ) : ℝ :=
  (gapT qp qpp (t+1) - gapT qp qpp t)
    + (gapS d (gapu a d e (t+1)) - gapS d (gapu a d e t))

/-- Semiconvergent denominators within a from-above block: `Q_t = t·q′ + q″`. -/
noncomputable def gapQ (qp qpp : ℝ) (t : ℝ) : ℝ := t * qp + qpp

/-- Gap exponent in CF variables: `x(t) = (a−t)·δ′ + δ_n`. -/
noncomputable def gapx (a d dn : ℝ) (t : ℝ) : ℝ := (a - t) * d + dn

/-- `S(λ) = sinh(λz)/sinh(z)` (C26 margins). -/
noncomputable def gapSfun (z lam : ℝ) : ℝ := Real.sinh (lam * z) / Real.sinh z

/-! ## C18b, T-half: second differences of the T-part -/

/-- Pure-algebra core of the T-part: for `A > c > 0`,
`(1+c/(A+c))·(1+c/(A−c)) / (1+c/A)² > 1`,
since the ratio equals `A³(A+2c)/((A+c)³(A−c))` and
`A³(A+2c) − (A+c)³(A−c) = c³(2A+c) > 0`. -/
theorem gapT_ratio_gt_one {A c : ℝ} (hc : 0 < c) (hAc : c < A) :
    1 < ((1 + c/(A+c)) * (1 + c/(A-c))) / (1 + c/A)^2 := by
  have hA : (0:ℝ) < A := by linarith
  have hA1 : (0:ℝ) < A + c := by linarith
  have hA2 : (0:ℝ) < A - c := by linarith
  have hden : (0:ℝ) < (A+c)^3 * (A-c) := by positivity
  have hident : A^3 * (A + 2*c) - (A+c)^3 * (A-c) = c^3 * (2*A + c) := by ring
  have hpos : (0:ℝ) < c^3 * (2*A + c) := by positivity
  have e1 : (1:ℝ) + c/(A+c) = (A + 2*c)/(A+c) := by field_simp; ring
  have e2 : (1:ℝ) + c/(A-c) = A/(A-c) := by field_simp; ring
  have e3 : (1:ℝ) + c/A = (A+c)/A := by field_simp
  have hratio : ((A + 2*c)/(A+c) * (A/(A-c))) / ((A+c)/A)^2
      = (A^3 * (A + 2*c)) / ((A+c)^3 * (A-c)) := by
    field_simp
  rw [e1, e2, e3, hratio, one_lt_div hden]
  linarith

/-- Second differences of the T-part are strictly positive (C18b, T-half). -/
theorem gapT_seconddiff_pos {t qp qpp : ℝ} (hqp : 0 < qp) (hqpp : 0 < qpp)
    (ht : 1 ≤ t) :
    0 < gapT qp qpp (t + 1) - 2 * gapT qp qpp t + gapT qp qpp (t - 1) := by
  have hAc : qp < t * qp + qpp := by
    have h1 : (0:ℝ) ≤ (t - 1) * qp := mul_nonneg (by linarith) (le_of_lt hqp)
    nlinarith
  have hA1pos : (0:ℝ) < (t+1) * qp + qpp := by nlinarith [ht, hqp, hqpp]
  have hAm1pos : (0:ℝ) < (t-1) * qp + qpp := by nlinarith [ht, hqp, hqpp]
  have hApos : (0:ℝ) < t * qp + qpp := by nlinarith [ht, hqp, hqpp]
  have h1 : (0:ℝ) < 1 + qp / ((t+1) * qp + qpp) := by
    have h : (0:ℝ) < qp / ((t+1) * qp + qpp) := by positivity
    linarith
  have h2 : (0:ℝ) < 1 + qp / ((t-1) * qp + qpp) := by
    have h : (0:ℝ) < qp / ((t-1) * qp + qpp) := by positivity
    linarith
  have h3 : (0:ℝ) < 1 + qp / (t * qp + qpp) := by
    have h : (0:ℝ) < qp / (t * qp + qpp) := by positivity
    linarith
  have hP : (0:ℝ) < (1 + qp / ((t+1) * qp + qpp)) * (1 + qp / ((t-1) * qp + qpp)) :=
    mul_pos h1 h2
  have hQ : (0:ℝ) < (1 + qp / (t * qp + qpp))^2 := by positivity
  have hdiff : gapT qp qpp (t+1) - 2 * gapT qp qpp t + gapT qp qpp (t-1)
      = Real.log (((1 + qp / ((t+1) * qp + qpp)) * (1 + qp / ((t-1) * qp + qpp)))
          / (1 + qp / (t * qp + qpp))^2) := by
    have eT1 : gapT qp qpp (t+1) = Real.log (1 + qp / ((t+1) * qp + qpp)) := rfl
    have eT2 : gapT qp qpp t = Real.log (1 + qp / (t * qp + qpp)) := rfl
    have eT3 : gapT qp qpp (t-1) = Real.log (1 + qp / ((t-1) * qp + qpp)) := rfl
    rw [eT1, eT2, eT3, Real.log_div (ne_of_gt hP) (ne_of_gt hQ),
      Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
    have hlog2 : 2 * Real.log (1 + qp / (t * qp + qpp))
        = Real.log ((1 + qp / (t * qp + qpp))^2) := by
      rw [pow_two, Real.log_mul (ne_of_gt h3) (ne_of_gt h3)]; ring
    rw [hlog2]
    ring
  rw [hdiff]
  have hratio := gapT_ratio_gt_one hqp hAc
  have hA1 : (t+1) * qp + qpp = (t * qp + qpp) + qp := by ring
  have hA2 : (t-1) * qp + qpp = (t * qp + qpp) - qp := by ring
  rw [hA1, hA2]
  exact Real.log_pos hratio

/-! ## C18b, S-half: second differences of the S-part -/

/-- Pure-algebra core of the S-part: for `X > c^2 > 1`,
`(X−c)³(Xc−1) − c(X−c²)(X−1)³ = (c−1)³·X·(X²−c) > 0`. -/
theorem gapS_ident {X c : ℝ} (hc : 1 < c) (hX : c^2 < X) :
    (0:ℝ) < (X-c)^3 * (X*c-1) - c * (X-c^2) * (X-1)^3 := by
  have hident : (X-c)^3 * (X*c-1) - c * (X-c^2) * (X-1)^3
      = (c-1)^3 * X * (X^2 - c) := by ring
  rw [hident]
  have hX1 : (1:ℝ) < X := by nlinarith [hX, hc, sq_nonneg (c - 1)]
  have hXpos : (0:ℝ) < X := by linarith
  have hXc : (0:ℝ) < X^2 - c := by
    have g1 : (0:ℝ) < X^2 - X := by
      have hmul := mul_pos hXpos (show (0:ℝ) < X - 1 by linarith)
      linarith
    have g3 : (0:ℝ) ≤ c^2 - c := by
      have hmul := mul_nonneg (show (0:ℝ) ≤ c by linarith) (show (0:ℝ) ≤ c - 1 by linarith)
      linarith
    linarith
  have hcsub : (0:ℝ) < c - 1 := by linarith
  positivity

/-- The S-part ratio exceeds 1: for `X > c^2 > 1`,
`((X/c−1)³(Xc−1))/(((X/c²−1)(X−1)³)) > 1`. -/
theorem gapS_ratio_gt_one {X c : ℝ} (hc : 1 < c) (hX : c^2 < X) :
    1 < ((X/c - 1)^3 * (X*c - 1)) / ((X/c^2 - 1) * (X-1)^3) := by
  have hc0 : (0:ℝ) < c := by linarith
  have hXc2 : (0:ℝ) < X - c^2 := by linarith
  have hX1 : (0:ℝ) < X - 1 := by nlinarith [hX, hc]
  have hXc : (0:ℝ) < X - c := by nlinarith [hX, hc]
  have hXc1 : (0:ℝ) < X * c - 1 := by nlinarith [hX, hc]
  have e1 : (X:ℝ)/c - 1 = (X - c)/c := by field_simp
  have e2 : (X:ℝ)/c^2 - 1 = (X - c^2)/c^2 := by field_simp
  have hden : (0:ℝ) < ((X - c^2)/c^2) * (X-1)^3 := by positivity
  have hratio : (((X-c)/c)^3 * (X*c-1)) / (((X-c^2)/c^2) * (X-1)^3)
      = ((X-c)^3 * (X*c-1)) / (c * (X-c^2) * (X-1)^3) := by
    field_simp
  rw [e1, e2, hratio, one_lt_div (by positivity : (0:ℝ) < c * (X-c^2) * (X-1)^3)]
  have h := gapS_ident hc hX
  linarith

/-- Second differences of the S-part are strictly positive (C18b, S-half):
for `v > 2d > 0`, `S(v−d) − 2S(v) + S(v+d) > 0`. -/
theorem gapS_seconddiff_pos {v d : ℝ} (hd : 0 < d) (hv : 2*d < v) :
    0 < gapS d (v-d) - 2 * gapS d v + gapS d (v+d) := by
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hc : (1:ℝ) < (2:ℝ)^d := by
    calc (1:ℝ) = (2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
      _ < (2:ℝ)^d := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hd
  have edd : ((2:ℝ)^d)^2 = (2:ℝ)^(d+d) := by
    rw [pow_two, ← Real.rpow_add h2pos]
  have hX : ((2:ℝ)^d)^2 < (2:ℝ)^v := by
    rw [edd]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hs1 : (2:ℝ)^(v-d) = (2:ℝ)^v / (2:ℝ)^d := Real.rpow_sub h2pos v d
  have hs2 : (2:ℝ)^(v+d) = (2:ℝ)^v * (2:ℝ)^d := Real.rpow_add h2pos v d
  have hs3 : (2:ℝ)^(v-2*d) = (2:ℝ)^v / ((2:ℝ)^d)^2 := by
    rw [show v - 2*d = v - (d+d) by ring, Real.rpow_sub h2pos, ← edd]
  have hp1 : (0:ℝ) < (2:ℝ)^(v-d) - 1 := by
    have h : (1:ℝ) < (2:ℝ)^(v-d) := by
      calc (1:ℝ) = (2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
        _ < (2:ℝ)^(v-d) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    linarith
  have hp2 : (0:ℝ) < (2:ℝ)^(v-2*d) - 1 := by
    have h : (1:ℝ) < (2:ℝ)^(v-2*d) := by
      calc (1:ℝ) = (2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
        _ < (2:ℝ)^(v-2*d) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    linarith
  have hp3 : (0:ℝ) < (2:ℝ)^v - 1 := by
    have h : (1:ℝ) < (2:ℝ)^v := by
      calc (1:ℝ) = (2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
        _ < (2:ℝ)^v := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    linarith
  have hp4 : (0:ℝ) < (2:ℝ)^(v+d) - 1 := by
    have h : (1:ℝ) < (2:ℝ)^(v+d) := by
      calc (1:ℝ) = (2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
        _ < (2:ℝ)^(v+d) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    linarith
  have eS1 : gapS d (v-d)
      = Real.log ((2:ℝ)^(v-d) - 1) - Real.log ((2:ℝ)^(v-2*d) - 1) := by
    unfold gapS
    rw [show (v-d)-d = v-2*d by ring, Real.log_div (ne_of_gt hp1) (ne_of_gt hp2)]
  have eS2 : gapS d v
      = Real.log ((2:ℝ)^v - 1) - Real.log ((2:ℝ)^(v-d) - 1) := by
    unfold gapS
    rw [Real.log_div (ne_of_gt hp3) (ne_of_gt hp1)]
  have eS3 : gapS d (v+d)
      = Real.log ((2:ℝ)^(v+d) - 1) - Real.log ((2:ℝ)^v - 1) := by
    unfold gapS
    rw [show (v+d)-d = v by ring, Real.log_div (ne_of_gt hp4) (ne_of_gt hp3)]
  have hP : (0:ℝ) < ((2:ℝ)^(v-d) - 1)^3 * ((2:ℝ)^(v+d) - 1) := by positivity
  have hQ : (0:ℝ) < ((2:ℝ)^(v-2*d) - 1) * ((2:ℝ)^v - 1)^3 := by positivity
  have hdiff : gapS d (v-d) - 2 * gapS d v + gapS d (v+d)
      = Real.log ((((2:ℝ)^(v-d) - 1)^3 * ((2:ℝ)^(v+d) - 1))
          / (((2:ℝ)^(v-2*d) - 1) * ((2:ℝ)^v - 1)^3)) := by
    rw [eS1, eS2, eS3, Real.log_div (ne_of_gt hP) (ne_of_gt hQ),
      Real.log_mul (ne_of_gt (by positivity : (0:ℝ) < ((2:ℝ)^(v-d) - 1)^3)) (ne_of_gt hp4),
      Real.log_mul (ne_of_gt hp2) (ne_of_gt (by positivity : (0:ℝ) < ((2:ℝ)^v - 1)^3)),
      Real.log_pow, Real.log_pow]
    ring
  rw [hdiff, hs1, hs2, hs3]
  exact Real.log_pos (gapS_ratio_gt_one hc hX)

/-! ## C18b proper: Δ(t) strictly increasing -/

/-- **C18b** (self-contained): `Δ(t) = lnG(t+1) − lnG(t)` is strictly
increasing on the block interior. `Δ(t+1) − Δ(t)` splits as the
T-second-difference at `t+1` plus the S-second-difference at `u(t+1)`. -/
theorem gapDelta_strictly_increasing {qp qpp a d e t : ℝ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (he : 0 < e)
    (ht1 : 1 ≤ t) (ht2 : t ≤ a - 3) :
    gapDelta qp qpp a d e t < gapDelta qp qpp a d e (t+1) := by
  have hT := gapT_seconddiff_pos hqp hqpp (show (1:ℝ) ≤ t + 1 by linarith)
  rw [show (t:ℝ) + 1 + 1 = t + 2 by ring, show (t:ℝ) + 1 - 1 = t by ring] at hT
  have hw : 2 * d < gapu a d e (t+1) := by
    have h2 : (2:ℝ) ≤ a - (t + 1) := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt hd)
    unfold gapu
    linarith
  have hS := gapS_seconddiff_pos hd hw
  rw [show gapu a d e (t+1) - d = gapu a d e (t+2) by unfold gapu; ring,
      show gapu a d e (t+1) + d = gapu a d e t by unfold gapu; ring] at hS
  have key : gapDelta qp qpp a d e (t+1) - gapDelta qp qpp a d e t
      = (gapT qp qpp (t+2) - 2 * gapT qp qpp (t+1) + gapT qp qpp t)
        + (gapS d (gapu a d e (t+2)) - 2 * gapS d (gapu a d e (t+1))
          + gapS d (gapu a d e t)) := by
    show ((gapT qp qpp (t+1+1) - gapT qp qpp (t+1))
        + (gapS d (gapu a d e (t+1+1)) - gapS d (gapu a d e (t+1))))
      - ((gapT qp qpp (t+1) - gapT qp qpp t)
        + (gapS d (gapu a d e (t+1)) - gapS d (gapu a d e t))) = _
    rw [show (t:ℝ) + 1 + 1 = t + 2 by ring]
    ring
  linarith

/-! ## CF wiring layer -/

/-- Q-determinant (C26 Lemma D2; also C22 Lemma 1's Q-part):
`Q_{t+2}·Q_t − Q_{t+1}² = −q′²`, by direct expansion
(the `q′q″` and `q″²` terms cancel). -/
theorem gapQ_det (qp qpp t : ℝ) :
    gapQ qp qpp (t+2) * gapQ qp qpp t - (gapQ qp qpp (t+1))^2 = -(qp^2) := by
  unfold gapQ; ring

/-- The exact Δ-sign criterion in CF variables (C22 Lemma 1, wired).
For `1 ≤ t`, `t+1 ≤ a−1`, with `Q_t = t·q′+q″`, `x(t) = (a−t)·δ′+δ_n`:
`Δ(t) < 0 ↔ (q′/Q_{t+1})·sinh(x(t+1)·ln2/2) > sinh(δ′·ln2/2)`.
This instantiates `gap_delta_sign_criterion` (the side conditions
`q′ < Q_{t+1}`, `δ′ < x(t+1)` follow from the CF positivity). -/
theorem gap_criterion_CF {qp qpp a d dn t : ℝ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (ht1 : 1 ≤ t) (ht2 : t + 1 ≤ a - 1) :
    Real.log (1 - (qp / gapQ qp qpp (t+1))^2)
      + Real.log (((2:ℝ)^(gapx a d dn (t+1)) - 1)^2
        / (((2:ℝ)^(gapx a d dn (t+1) + d) - 1) * ((2:ℝ)^(gapx a d dn (t+1) - d) - 1)))
      < 0
    ↔ Real.sinh (d * Real.log 2 / 2)
        < (qp / gapQ qp qpp (t+1)) * Real.sinh (gapx a d dn (t+1) * Real.log 2 / 2) := by
  have hQ : qp < gapQ qp qpp (t+1) := by
    have h1 : (0:ℝ) ≤ (t+1-1) * qp := mul_nonneg (by linarith) (le_of_lt hqp)
    unfold gapQ; linarith
  have hv : d < gapx a d dn (t+1) := by
    have h2 : (0:ℝ) ≤ (a - (t+1) - 1) * d := mul_nonneg (by linarith) (le_of_lt hd)
    unfold gapx; linarith
  exact gap_delta_sign_criterion _ _ _ _ hqp hQ hd hv

/-! ## The criterion's equality case -/

/-- Equality case of the exact Δ-sign criterion (C22 Lemma 1):
`Δ(t) = 0 ↔ (q′/Q)·sinh(x(t+1)·ln2/2) = sinh(δ′·ln2/2)`.
Follows the `gap_delta_sign_criterion` chain with `=` in place of `<`:
`ln P = 0 ↔ P = 1` (`Real.log_eq_zero`), cross-multiplication, the same
ring identity, `sq_eq_sq₀` (both sides nonneg), division by `2Q√w > 0`. -/
theorem gap_delta_sign_criterion_eq
    (Q q v d : ℝ) (hq : 0 < q) (hQ : q < Q) (hd : 0 < d) (hv : d < v) :
    Real.log (1 - (q / Q) ^ 2) +
      Real.log (((2:ℝ) ^ v - 1) ^ 2 /
        (((2:ℝ) ^ (v + d) - 1) * ((2:ℝ) ^ (v - d) - 1))) = 0
    ↔ Real.sinh (d * Real.log 2 / 2) = (q / Q) * Real.sinh (v * Real.log 2 / 2) := by
  have hQpos : (0:ℝ) < Q := lt_trans hq hQ
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
  -- Product form.
  have hPdiv : (0:ℝ) < (w - 1) ^ 2 / (w ^ 2 - 2 * w * Real.cosh u + 1) := by
    rw [← hD]; exact hB
  have hP : (0:ℝ) < (1 - (q / Q) ^ 2) * ((w - 1) ^ 2 / (w ^ 2 - 2 * w * Real.cosh u + 1)) :=
    mul_pos hA hPdiv
  rw [hD, ← Real.log_mul (ne_of_gt hA) (ne_of_gt hPdiv)]
  -- `ln P = 0 ↔ P = 1`.
  have hlog0 : Real.log ((1 - (q / Q) ^ 2) * ((w - 1) ^ 2 / (w ^ 2 - 2 * w * Real.cosh u + 1))) = 0
      ↔ (1 - (q / Q) ^ 2) * ((w - 1) ^ 2 / (w ^ 2 - 2 * w * Real.cosh u + 1)) = 1 := by
    rw [Real.log_eq_zero]
    constructor
    · rintro (h | h | h)
      · exact absurd h (ne_of_gt hP)
      · exact h
      · linarith
    · intro h; exact Or.inr (Or.inl h)
  rw [hlog0]
  -- Step 1 (=): cross-multiply.
  have h1 : (1:ℝ) - (q / Q) ^ 2 = (Q ^ 2 - q ^ 2) / Q ^ 2 := by
    field_simp
  have hden : (0:ℝ) < Q ^ 2 * (w ^ 2 - 2 * w * Real.cosh u + 1) := by positivity
  have step1 : (1 - (q / Q) ^ 2) * ((w - 1) ^ 2 / (w ^ 2 - 2 * w * Real.cosh u + 1)) = 1
      ↔ (Q ^ 2 - q ^ 2) * (w - 1) ^ 2 = Q ^ 2 * (w ^ 2 - 2 * w * Real.cosh u + 1) := by
    rw [h1, div_mul_div_comm, div_eq_iff (ne_of_gt hden), one_mul]
  rw [step1]
  -- Step 2 (=): the ring identity.
  have heq : (Q ^ 2 - q ^ 2) * (w - 1) ^ 2 - Q ^ 2 * (w ^ 2 - 2 * w * Real.cosh u + 1)
      = 2 * Q ^ 2 * w * (Real.cosh u - 1) - q ^ 2 * (w - 1) ^ 2 := by ring
  have step2 : (Q ^ 2 - q ^ 2) * (w - 1) ^ 2 = Q ^ 2 * (w ^ 2 - 2 * w * Real.cosh u + 1)
      ↔ 2 * Q ^ 2 * w * (Real.cosh u - 1) = q ^ 2 * (w - 1) ^ 2 := by
    constructor <;> intro h <;> linarith
  rw [step2]
  -- Step 3 (=): square roots, both sides nonneg.
  have hcosh1 : Real.cosh u - 1 = 2 * Real.sinh (u / 2) ^ 2 := by
    have h2u : (2:ℝ) * (u / 2) = u := by ring
    have hc1 : Real.cosh u = 2 * Real.cosh (u / 2) ^ 2 - 1 := by
      conv_lhs => rw [← h2u, Real.cosh_two_mul]
      rw [Real.sinh_sq]
      ring
    have hs := Real.sinh_sq (u / 2)
    linarith
  have hsu : (0:ℝ) < Real.sinh (u / 2) :=
    Real.sinh_pos_iff.mpr (by rw [hu_def]; positivity)
  have hsu_nn : (0:ℝ) ≤ 2 * Q * Real.sqrt w * Real.sinh (u / 2) := by positivity
  have hqw_nn : (0:ℝ) ≤ q * (w - 1) :=
    mul_nonneg (le_of_lt hq) (by linarith : (0:ℝ) ≤ w - 1)
  have e1 : (2 * Q * Real.sqrt w * Real.sinh (u / 2)) ^ 2
      = 2 * Q ^ 2 * w * (2 * Real.sinh (u / 2) ^ 2) := by
    simp only [mul_pow, Real.sq_sqrt (le_of_lt hwpos)]
    ring
  have e2 : (q * (w - 1)) ^ 2 = q ^ 2 * (w - 1) ^ 2 := by ring
  have step3 : 2 * Q ^ 2 * w * (Real.cosh u - 1) = q ^ 2 * (w - 1) ^ 2
      ↔ 2 * Q * Real.sqrt w * Real.sinh (u / 2) = q * (w - 1) := by
    rw [hcosh1, ← e1, ← e2, sq_eq_sq₀ hsu_nn hqw_nn]
  rw [step3]
  -- Step 4 (=): divide by `2Q√w > 0`.
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
  have step4 : 2 * Q * Real.sqrt w * Real.sinh (u / 2) = q * (w - 1)
      ↔ Real.sinh (u / 2) = (q / Q) * Real.sinh (v * Real.log 2 / 2) := by
    rw [← hsinh_id]
    have hrhs : (q / Q) * ((w - 1) / (2 * Real.sqrt w))
        = (q * (w - 1)) / (Q * (2 * Real.sqrt w)) := div_mul_div_comm _ _ _ _
    have hpos : (0:ℝ) < Q * (2 * Real.sqrt w) := by positivity
    rw [hrhs, eq_div_iff (ne_of_gt hpos)]
    have key : 2 * Q * Real.sqrt w * Real.sinh (u / 2)
        = Real.sinh (u / 2) * (Q * (2 * Real.sqrt w)) := by ring
    rw [key]
  rw [step4]

/-! ## C26 margin duality: the margin chain -/

/-- The lower exact-criterion margin: `M⁻ = (q′/Q_{m−1})·S(m+1+ρ)`. -/
noncomputable def gapMminus (qp qpp z m rho : ℝ) : ℝ :=
  (qp / gapQ qp qpp (m-1)) * gapSfun z (m+1+rho)

/-- The upper exact-criterion margin: `M⁺ = (Q_{m+1}/q′)/S(m−1+ρ)`. -/
noncomputable def gapMplus (qp qpp z m rho : ℝ) : ℝ :=
  (gapQ qp qpp (m+1) / qp) / gapSfun z (m-1+rho)

/-- The margin bridge: `M0 = (q′/Q_m)·S(m+ρ)`. -/
noncomputable def gapM0 (qp qpp z m rho : ℝ) : ℝ :=
  (qp / gapQ qp qpp m) * gapSfun z (m+rho)

/-- C26 margin chain (algebraic core): `M⁻ ⋚ M⁺ ↔ M0 ⋚ 1`.
`M⁻ < M⁺ ↔ S(m+1+ρ)·S(m−1+ρ) < Q_{m−1}·Q_{m+1}/q′²`
(multiply by `(Q_{m−1}/q′)·S(m−1+ρ) > 0`), then D1
(`gap_sinh_product_identity`) and D2 (`gapQ_det`) give
`S(m+ρ)²−1 < (Q_m²−q′²)/q′²`, i.e. `(q′/Q_m)·S(m+ρ) < 1`. -/
theorem gap_margin_chain {m qp qpp z rho : ℝ} (hm : 3 ≤ m)
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hz : 0 < z) (hrho : 0 < rho) :
    (gapMminus qp qpp z m rho < gapMplus qp qpp z m rho ↔ gapM0 qp qpp z m rho < 1)
    ∧ (gapMminus qp qpp z m rho > gapMplus qp qpp z m rho ↔ gapM0 qp qpp z m rho > 1)
    ∧ (gapMminus qp qpp z m rho = gapMplus qp qpp z m rho ↔ gapM0 qp qpp z m rho = 1) := by
  have hsz : (0:ℝ) < Real.sinh z := Real.sinh_pos_iff.mpr hz
  have hszne : Real.sinh z ≠ 0 := ne_of_gt hsz
  have hlam1 : (0:ℝ) < m+1+rho := by linarith
  have hlam2 : (0:ℝ) < m-1+rho := by linarith
  have hlam0 : (0:ℝ) < m+rho := by linarith
  have hs1 : (0:ℝ) < gapSfun z (m+1+rho) := by
    unfold gapSfun; exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hlam1 hz)) hsz
  have hsm1 : (0:ℝ) < gapSfun z (m-1+rho) := by
    unfold gapSfun; exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hlam2 hz)) hsz
  have hs0 : (0:ℝ) < gapSfun z (m+rho) := by
    unfold gapSfun; exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hlam0 hz)) hsz
  have hQm1 : (0:ℝ) < gapQ qp qpp (m-1) := by
    have h2 : (2:ℝ) ≤ m - 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_right h2 (le_of_lt hqp)
    unfold gapQ; linarith
  have hQm : (0:ℝ) < gapQ qp qpp m := by
    have h2 : (3:ℝ) ≤ m := by linarith
    have hmul := mul_le_mul_of_nonneg_right h2 (le_of_lt hqp)
    unfold gapQ; linarith
  have hQm1ne : gapQ qp qpp (m-1) ≠ 0 := ne_of_gt hQm1
  have hqpne : qp ≠ 0 := ne_of_gt hqp
  have hsm1ne : gapSfun z (m-1+rho) ≠ 0 := ne_of_gt hsm1
  -- D1 with `lam = m+rho`.
  have hD1 := gap_sinh_product_identity z (m+rho) hszne
  have eD1 : gapSfun z (m+1+rho) * gapSfun z (m-1+rho)
      = (gapSfun z (m+rho))^2 - 1 := by
    rw [show m+1+rho = (m+rho)+1 by ring, show m-1+rho = (m+rho)-1 by ring]
    exact hD1
  -- D2 at `t = m-1`.
  have hD2 := gapQ_det qp qpp (m-1)
  have eD2 : gapQ qp qpp (m-1) * gapQ qp qpp (m+1)
      = (gapQ qp qpp m)^2 - qp^2 := by
    rw [show (m:ℝ)-1+2 = m+1 by ring, show (m:ℝ)-1+1 = m by ring] at hD2
    linarith
  -- The common positive multiplier and the two product forms.
  have hmul : (0:ℝ) < (gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho) :=
    mul_pos (div_pos hQm1 hqp) hsm1
  have hQQ : (qp / gapQ qp qpp (m-1)) * (gapQ qp qpp (m-1) / qp) = 1 := by
    rw [div_mul_div_comm, mul_comm (gapQ qp qpp (m - 1)) qp,
      div_self (ne_of_gt (mul_pos hqp hQm1))]
  have eL : gapMminus qp qpp z m rho * ((gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho))
      = gapSfun z (m+1+rho) * gapSfun z (m-1+rho) := by
    unfold gapMminus
    calc (qp / gapQ qp qpp (m-1)) * gapSfun z (m+1+rho)
          * ((gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho))
        = ((qp / gapQ qp qpp (m-1)) * (gapQ qp qpp (m-1)/qp))
          * (gapSfun z (m+1+rho) * gapSfun z (m-1+rho)) := by ring
      _ = gapSfun z (m+1+rho) * gapSfun z (m-1+rho) := by rw [hQQ, one_mul]
  have hsm1c : ((gapQ qp qpp (m+1)/qp) / gapSfun z (m-1+rho)) * gapSfun z (m-1+rho)
      = gapQ qp qpp (m+1)/qp := div_mul_cancel₀ _ hsm1ne
  have eR : gapMplus qp qpp z m rho * ((gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho))
      = gapQ qp qpp (m-1) * gapQ qp qpp (m+1) / qp^2 := by
    unfold gapMplus
    calc (gapQ qp qpp (m+1)/qp / gapSfun z (m-1+rho))
          * ((gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho))
        = (((gapQ qp qpp (m+1)/qp) / gapSfun z (m-1+rho)) * gapSfun z (m-1+rho))
          * (gapQ qp qpp (m-1)/qp) := by ring
      _ = (gapQ qp qpp (m+1)/qp) * (gapQ qp qpp (m-1)/qp) := by rw [hsm1c]
      _ = gapQ qp qpp (m-1) * gapQ qp qpp (m+1) / qp^2 := by
          rw [div_mul_div_comm, pow_two]; congr 1; ring
  -- Step A: multiply through by the positive factor.
  have stepAlt : gapMminus qp qpp z m rho < gapMplus qp qpp z m rho
      ↔ gapSfun z (m+1+rho) * gapSfun z (m-1+rho)
        < gapQ qp qpp (m-1) * gapQ qp qpp (m+1) / qp^2 := by
    constructor
    · intro h
      have h2 := mul_lt_mul_of_pos_right h hmul
      rwa [eL, eR] at h2
    · intro h
      have h2 : gapMminus qp qpp z m rho * ((gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho))
          < gapMplus qp qpp z m rho * ((gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho)) := by
        rwa [eL, eR]
      exact lt_of_mul_lt_mul_right h2 (le_of_lt hmul)
  have stepAgt : gapMminus qp qpp z m rho > gapMplus qp qpp z m rho
      ↔ gapSfun z (m+1+rho) * gapSfun z (m-1+rho)
        > gapQ qp qpp (m-1) * gapQ qp qpp (m+1) / qp^2 := by
    rw [gt_iff_lt, gt_iff_lt]
    constructor
    · intro h
      have h2 := mul_lt_mul_of_pos_right h hmul
      rwa [eL, eR] at h2
    · intro h
      have h2 : gapMplus qp qpp z m rho * ((gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho))
          < gapMminus qp qpp z m rho * ((gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho)) := by
        rwa [eL, eR]
      exact lt_of_mul_lt_mul_right h2 (le_of_lt hmul)
  have stepAeq : gapMminus qp qpp z m rho = gapMplus qp qpp z m rho
      ↔ gapSfun z (m+1+rho) * gapSfun z (m-1+rho)
        = gapQ qp qpp (m-1) * gapQ qp qpp (m+1) / qp^2 := by
    constructor
    · intro h
      have h2 := congrArg (· * ((gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho))) h
      rwa [eL, eR] at h2
    · intro h
      have h2 : gapMminus qp qpp z m rho * ((gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho))
          = gapMplus qp qpp z m rho * ((gapQ qp qpp (m-1)/qp) * gapSfun z (m-1+rho)) := by
        rwa [eL, eR]
      exact mul_right_cancel₀ (ne_of_gt hmul) h2
  -- Step B: D1 + D2, then take square roots.
  have hqp2 : (0:ℝ) < qp^2 := by positivity
  have hs0nn : (0:ℝ) ≤ gapSfun z (m+rho) * qp :=
    mul_nonneg (le_of_lt hs0) (le_of_lt hqp)
  have hQmnn : (0:ℝ) ≤ gapQ qp qpp m := le_of_lt hQm
  have eM0 : gapM0 qp qpp z m rho = (qp * gapSfun z (m+rho)) / gapQ qp qpp m := by
    unfold gapM0; rw [div_mul_eq_mul_div]
  have stepBlt : gapSfun z (m+1+rho) * gapSfun z (m-1+rho)
        < gapQ qp qpp (m-1) * gapQ qp qpp (m+1) / qp^2
      ↔ gapM0 qp qpp z m rho < 1 := by
    rw [eD1, eD2, lt_div_iff₀ hqp2, eM0, div_lt_iff₀ hQm, one_mul]
    constructor
    · intro h
      have h1 : (gapSfun z (m+rho) * qp)^2 < (gapQ qp qpp m)^2 := by nlinarith [h]
      have h2 := (sq_lt_sq₀ hs0nn hQmnn).mp h1
      linarith [h2]
    · intro h
      have h2 : gapSfun z (m+rho) * qp < gapQ qp qpp m := by linarith [h]
      have h1 := (sq_lt_sq₀ hs0nn hQmnn).mpr h2
      nlinarith [h1]
  have stepBgt : gapSfun z (m+1+rho) * gapSfun z (m-1+rho)
        > gapQ qp qpp (m-1) * gapQ qp qpp (m+1) / qp^2
      ↔ gapM0 qp qpp z m rho > 1 := by
    rw [gt_iff_lt, eD1, eD2, div_lt_iff₀ hqp2, eM0]
    have hM0gt : (qp * gapSfun z (m+rho)) / gapQ qp qpp m > 1
        ↔ qp * gapSfun z (m+rho) > gapQ qp qpp m := by
      rw [gt_iff_lt, lt_div_iff₀ hQm, one_mul]
    rw [hM0gt]
    constructor
    · intro h
      have h1 : (gapQ qp qpp m)^2 < (gapSfun z (m+rho) * qp)^2 := by nlinarith [h]
      have h2 := (sq_lt_sq₀ hQmnn hs0nn).mp h1
      linarith [h2]
    · intro h
      have h2 : gapQ qp qpp m < gapSfun z (m+rho) * qp := by linarith [h]
      have h1 := (sq_lt_sq₀ hQmnn hs0nn).mpr h2
      nlinarith [h1]
  have stepBeq : gapSfun z (m+1+rho) * gapSfun z (m-1+rho)
        = gapQ qp qpp (m-1) * gapQ qp qpp (m+1) / qp^2
      ↔ gapM0 qp qpp z m rho = 1 := by
    rw [eD1, eD2, eM0, eq_div_iff (ne_of_gt hqp2), div_eq_iff (ne_of_gt hQm), one_mul]
    constructor
    · intro h
      have h1 : (gapSfun z (m+rho) * qp)^2 = (gapQ qp qpp m)^2 := by
        have e : (gapSfun z (m+rho) * qp)^2 = (gapSfun z (m+rho))^2 * qp^2 := by ring
        rw [e]; linarith [h]
      have h2 := (sq_eq_sq₀ hs0nn hQmnn).mp h1
      linarith [h2]
    · intro h
      have h2 : gapSfun z (m+rho) * qp = gapQ qp qpp m := by linarith [h]
      have h1 := (sq_eq_sq₀ hs0nn hQmnn).mpr h2
      have e : ((gapSfun z (m+rho))^2 - 1) * qp^2
          = (gapSfun z (m+rho) * qp)^2 - qp^2 := by ring
      rw [e, h1]
  exact ⟨stepAlt.trans stepBlt, stepAgt.trans stepBgt, stepAeq.trans stepBeq⟩

/-! ## C26 full duality -/

/-- `Δ(m−1)` in exact log form (the criterion's LHS at `t = m−1`,
i.e. `Q = Q_m`, `v = x(m)`, `d = δ′`). -/
noncomputable def gapDeltaLog (qp qpp d dn m : ℝ) : ℝ :=
  Real.log (1 - (qp / gapQ qp qpp m)^2)
    + Real.log (((2:ℝ)^(gapx (2*m) d dn m) - 1)^2
      / (((2:ℝ)^(gapx (2*m) d dn m + d) - 1) * ((2:ℝ)^(gapx (2*m) d dn m - d) - 1)))

/-- The `>` case of the Δ-sign criterion trichotomy:
`0 < Δlog ↔ (q/Q)·sinh(v·ln2/2) < sinh(d·ln2/2)`.
From `gap_delta_sign_criterion` (< case) + `gap_delta_sign_criterion_eq` (= case). -/
theorem gap_delta_sign_gt (Q q v d : ℝ) (hq : 0 < q) (hQ : q < Q) (hd : 0 < d) (hv : d < v) :
    0 < Real.log (1 - (q / Q) ^ 2) +
      Real.log (((2:ℝ) ^ v - 1) ^ 2 /
        (((2:ℝ) ^ (v + d) - 1) * ((2:ℝ) ^ (v - d) - 1)))
    ↔ (q / Q) * Real.sinh (v * Real.log 2 / 2) < Real.sinh (d * Real.log 2 / 2) := by
  have h1 := gap_delta_sign_criterion Q q v d hq hQ hd hv
  have h2 := gap_delta_sign_criterion_eq Q q v d hq hQ hd hv
  constructor
  · intro hpos
    by_contra hcon
    push Not at hcon
    rcases le_iff_lt_or_eq.mp hcon with hlt | heq
    · have h3 := h1.mpr hlt; linarith
    · have h3 := h2.mpr heq; linarith
  · intro hlt
    by_contra hcon
    push Not at hcon
    rcases le_iff_lt_or_eq.mp hcon with hlt2 | heq
    · have h3 := h1.mp hlt2; linarith
    · have h3 := h2.mp heq; linarith

/-- Margin bridge: `M0 ⋚ 1 ↔ (q′/Q_m)·sinh(x(m)·ln2/2) ⋚ sinh(δ′·ln2/2)`.
`M0 = (q′/Q_m)·sinh((m+ρ)z)/sinh(z)` and `(m+ρ)·z = x(m)·ln2/2`
since `x(m) = (m+ρ)·δ′` (with `z = δ′·ln2/2`, `ρ = δ_n/δ′`). -/
theorem gap_M0_bridge {m qp qpp d dn : ℝ} (_hm : 3 ≤ m)
    (_hqp : 0 < qp) (_hqpp : 0 < qpp) (hd : 0 < d) (_hdn : 0 < dn) :
    (gapM0 qp qpp (d*Real.log 2/2) m (dn/d) < 1
      ↔ (qp/gapQ qp qpp m)*Real.sinh (gapx (2*m) d dn m*Real.log 2/2) < Real.sinh (d*Real.log 2/2))
    ∧ (gapM0 qp qpp (d*Real.log 2/2) m (dn/d) > 1
      ↔ (qp/gapQ qp qpp m)*Real.sinh (gapx (2*m) d dn m*Real.log 2/2) > Real.sinh (d*Real.log 2/2))
    ∧ (gapM0 qp qpp (d*Real.log 2/2) m (dn/d) = 1
      ↔ (qp/gapQ qp qpp m)*Real.sinh (gapx (2*m) d dn m*Real.log 2/2) = Real.sinh (d*Real.log 2/2)) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hzpos : (0:ℝ) < d * Real.log 2 / 2 := by positivity
  have hsz : (0:ℝ) < Real.sinh (d * Real.log 2 / 2) := Real.sinh_pos_iff.mpr hzpos
  have hdne : d ≠ 0 := ne_of_gt hd
  have hxm : gapx (2*m) d dn m = (m + dn/d) * d := by
    unfold gapx
    rw [show (2:ℝ)*m - m = m by ring, add_mul, div_mul_cancel₀ _ hdne]
  have harg : (m + dn/d) * (d * Real.log 2 / 2)
      = gapx (2*m) d dn m * Real.log 2 / 2 := by
    have h : (m + dn/d) * (d * Real.log 2 / 2) = ((m + dn/d) * d) * Real.log 2 / 2 := by ring
    rw [h, hxm]
  have hM0eq : gapM0 qp qpp (d*Real.log 2/2) m (dn/d)
      = (qp/gapQ qp qpp m) * (Real.sinh ((m + dn/d)*(d*Real.log 2/2)) / Real.sinh (d*Real.log 2/2)) := rfl
  have core_lt : (qp/gapQ qp qpp m) * (Real.sinh ((m + dn/d)*(d*Real.log 2/2)) / Real.sinh (d*Real.log 2/2)) < 1
      ↔ (qp/gapQ qp qpp m) * Real.sinh ((m + dn/d)*(d*Real.log 2/2)) < Real.sinh (d*Real.log 2/2) := by
    rw [mul_div_assoc', div_lt_iff₀ hsz, one_mul]
  have core_gt : (qp/gapQ qp qpp m) * (Real.sinh ((m + dn/d)*(d*Real.log 2/2)) / Real.sinh (d*Real.log 2/2)) > 1
      ↔ (qp/gapQ qp qpp m) * Real.sinh ((m + dn/d)*(d*Real.log 2/2)) > Real.sinh (d*Real.log 2/2) := by
    rw [gt_iff_lt, mul_div_assoc', lt_div_iff₀ hsz, one_mul, gt_iff_lt]
  have core_eq : (qp/gapQ qp qpp m) * (Real.sinh ((m + dn/d)*(d*Real.log 2/2)) / Real.sinh (d*Real.log 2/2)) = 1
      ↔ (qp/gapQ qp qpp m) * Real.sinh ((m + dn/d)*(d*Real.log 2/2)) = Real.sinh (d*Real.log 2/2) := by
    rw [mul_div_assoc', div_eq_iff (ne_of_gt hsz), one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hM0eq, core_lt, harg]
  · rw [hM0eq, core_gt, harg]
  · rw [hM0eq, core_eq, harg]

/-- **C26 margin duality** (full): on a from-above block with `a = 2m`, `m ≥ 3`,
with `z = δ′·ln2/2`, `ρ = δ_n/δ′`:
`M⁻ < M⁺ ↔ Δ(m−1) > 0`, `M⁻ > M⁺ ↔ Δ(m−1) < 0`, `M⁻ = M⁺ ↔ Δ(m−1) = 0`.
Via `gap_margin_chain` (D1 + D2), `gap_M0_bridge`, and the criterion
trichotomy (`gap_delta_sign_criterion`, `gap_delta_sign_criterion_eq`,
`gap_delta_sign_gt`). Zero Diophantine input. -/
theorem gap_margin_duality {m qp qpp d dn : ℝ} (hm : 3 ≤ m)
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn) :
    (gapMminus qp qpp (d*Real.log 2/2) m (dn/d) < gapMplus qp qpp (d*Real.log 2/2) m (dn/d)
      ↔ 0 < gapDeltaLog qp qpp d dn m)
    ∧ (gapMminus qp qpp (d*Real.log 2/2) m (dn/d) > gapMplus qp qpp (d*Real.log 2/2) m (dn/d)
      ↔ gapDeltaLog qp qpp d dn m < 0)
    ∧ (gapMminus qp qpp (d*Real.log 2/2) m (dn/d) = gapMplus qp qpp (d*Real.log 2/2) m (dn/d)
      ↔ gapDeltaLog qp qpp d dn m = 0) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hz : (0:ℝ) < d * Real.log 2 / 2 := by positivity
  have hrho : (0:ℝ) < dn / d := div_pos hdn hd
  have hchain := gap_margin_chain hm hqp hqpp hz hrho
  have hbridge := gap_M0_bridge hm hqp hqpp hd hdn
  have hQm : qp < gapQ qp qpp m := by
    have h2 : (3:ℝ) ≤ m := by linarith
    have hmul := mul_le_mul_of_nonneg_right h2 (le_of_lt hqp)
    unfold gapQ; linarith
  have hvm : d < gapx (2*m) d dn m := by
    have h3 : (0:ℝ) ≤ (m-1) * d := mul_nonneg (by linarith) (le_of_lt hd)
    unfold gapx; nlinarith
  have hgt := gap_delta_sign_gt (gapQ qp qpp m) qp (gapx (2*m) d dn m) d hqp hQm hd hvm
  have hlt := gap_delta_sign_criterion (gapQ qp qpp m) qp (gapx (2*m) d dn m) d hqp hQm hd hvm
  have heq := gap_delta_sign_criterion_eq (gapQ qp qpp m) qp (gapx (2*m) d dn m) d hqp hQm hd hvm
  have hlog_eq : gapDeltaLog qp qpp d dn m
      = Real.log (1 - (qp / gapQ qp qpp m)^2) +
        Real.log (((2:ℝ)^(gapx (2*m) d dn m) - 1)^2 /
          (((2:ℝ)^(gapx (2*m) d dn m + d) - 1) * ((2:ℝ)^(gapx (2*m) d dn m - d) - 1))) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hchain.1, hbridge.1, hlog_eq]
    exact hgt.symm
  · rw [hchain.2.1, hbridge.2.1, hlog_eq]
    exact hlt.symm
  · rw [hchain.2.2, hbridge.2.2, hlog_eq]
    exact (eq_comm.trans heq.symm)
