import Mathproofs.CollatzGapC23

/-!
# C22 / C25 / C26 assembly: the gap-factor argmin batch (R97)

Source hand proofs: `~/workspace/math-unsolved/c22_proofs_r24.md` (C22, Round 24),
`~/workspace/math-unsolved/c25_proofs_r33.md` (C25, Round 33),
`~/workspace/math-unsolved/c26_proofs_r36.md` (C26, Round 36).

This module machine-checks the remaining `[PROVED*]` members of the gap-factor
batch:
- **C22 Theorem 3** (odd-a argmin): `t* ≥ m` unconditionally (`c22_lower`),
  and `Δ(m) > 0` under the explicit `L(n)` condition, hence `t* = m`
  (`c22_delta_pos_at`, `c22_upper`);
- **C25(a)** (even-a lower bracket): `t* ≥ m−1` unconditionally, zero
  Diophantine input (`c25a`);
- **C25(b)** (even-a upper bracket): `t* ≤ m` under the explicit checkable
  `q′² ≥ (ln2)²(m+1)/96` (`c25b`);
- **C26 corollaries a/b/c**: margin-order readings of the argmin
  (`c26a`, `c26b`, `c26c`).

Building blocks (all `[PROVED]`): `gap_criterion_CF` / `gap_delta_sign_gt`
(the exact Δ-sign criterion), `sinh_scaling_gt` (sub-lemma S: sinh
superlinearity), `gap_sinh_le_mul_exp` (sub-lemma E: sinh upper envelope),
`sinh_ge_id`, `gap_log_one_add_ge`, `delta'_formula` (C24 Lemma 1 in block
form), `gapDelta_strictly_increasing` (C18b), `gap_margin_duality` (C26 proper),
`c23a` / `c23b` (C23 assembly), `cf_selector_ne` (C24 strict dichotomy).

Convention: every assembled theorem takes the CF/analysis variable
identifications and the `Δ = g(t+1) − g(t)` bridge as explicit hypotheses,
in the style of `c23a` / `c23b`.

Checked with Lean 4.34.1 + Mathlib v4.34.1 on xavier (R101):
c26a/c26b/c26c, gapDeltaLogT_pos/neg_chain, log_one_add_div_one_sub_ge all
sorry-free, standard axioms only. R105: c22_delta_pos_at (Steps A–E, with
R101's corrected hL) [PROVED] — machine-checked, standard axioms only,
zero sorrys in the module.
-/

namespace GapCF

/-! ## The criterion's log form at general index -/

/-- `Δ(t)` in exact log form at general index `t`: the LHS of
`gap_criterion_CF`. At `t = m−1`, `a = 2m` this is `gapDeltaLog`. -/
noncomputable def gapDeltaLogT (qp qpp d dn a t : ℝ) : ℝ :=
  Real.log (1 - (qp / gapQ qp qpp (t+1))^2)
    + Real.log (((2:ℝ)^(gapx a d dn (t+1)) - 1)^2
      / (((2:ℝ)^(gapx a d dn (t+1) + d) - 1) * ((2:ℝ)^(gapx a d dn (t+1) - d) - 1)))

/-- General `gapDelta = gapDeltaLogT` bridge (generalizes
`gapDelta_gapDeltaLog`): the T-diff + S-diff form of `Δ(t)` equals the
criterion's log-sum at every index. -/
theorem gapDelta_eq_gapDeltaLogT {qp qpp a d e t : ℝ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (he : 0 < e)
    (ht1 : 1 ≤ t) (hta : t + 2 ≤ a) :
    gapDelta qp qpp a d e t = gapDeltaLogT qp qpp d e a t := by
  have hnn : (0:ℝ) ≤ (a - (t+1) - 1) * d :=
    mul_nonneg (by linarith) hd.le
  have hv : (0:ℝ) < gapx a d e (t+1) := by
    unfold gapx
    linarith [he]
  have hvd : (0:ℝ) < gapx a d e (t+1) - d := by
    unfold gapx
    linarith [he]
  have hQ1 : (0:ℝ) < gapQ qp qpp (t+1) := by
    unfold gapQ
    have h1 : (0:ℝ) ≤ (t+1) * qp := mul_nonneg (by linarith) hqp.le
    linarith [hqpp]
  have hQ0 : (0:ℝ) < gapQ qp qpp t := by
    unfold gapQ
    have h1 : (0:ℝ) ≤ t * qp := mul_nonneg (by linarith) hqp.le
    linarith [hqpp]
  have hS1 : (1:ℝ) < (2:ℝ)^(gapx a d e (t+1)) :=
    calc (1:ℝ) = (2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
      _ < (2:ℝ)^(gapx a d e (t+1)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hv
  have hS2 : (1:ℝ) < (2:ℝ)^(gapx a d e (t+1) - d) :=
    calc (1:ℝ) = (2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
      _ < (2:ℝ)^(gapx a d e (t+1) - d) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hvd
  have hS3 : (1:ℝ) < (2:ℝ)^(gapx a d e (t+1) + d) :=
    calc (1:ℝ) = (2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
      _ < (2:ℝ)^(gapx a d e (t+1) + d) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith [hv, hd])
  have hu1 : gapu a d e (t+1) = gapx a d e (t+1) := by unfold gapu gapx; ring
  have hu2 : gapu a d e t = gapx a d e (t+1) + d := by unfold gapu gapx; ring
  have hS := gapS_diff_eq hS1 hS2 hS3
  have hQ0' : (0:ℝ) < gapQ qp qpp ((t+1)-1) := by
    have e : (t:ℝ)+1-1 = t := by ring
    rw [e]; exact hQ0
  have hT := gapT_diff_eq (m := t+1) hqp hQ1 hQ0'
  have hT2 : gapT qp qpp (t+1) - gapT qp qpp t
      = Real.log (1 - (qp/gapQ qp qpp (t+1))^2) := by
    have e : (t:ℝ)+1-1 = t := by ring
    rw [e] at hT
    exact hT
  have hdelta : gapDelta qp qpp a d e t
      = (gapT qp qpp (t+1) - gapT qp qpp t)
        + (gapS d (gapx a d e (t+1)) - gapS d (gapx a d e (t+1) + d)) := by
    unfold gapDelta
    rw [hu1, hu2]
  rw [hdelta, hT2, hS]
  rfl

/-- Strict increase of the log-form `Δ` (transport of C18b
`gapDelta_strictly_increasing` across the bridge). -/
theorem gapDeltaLogT_mono {qp qpp a d e t : ℝ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (he : 0 < e)
    (ht1 : 1 ≤ t) (ht2 : t ≤ a - 3) :
    gapDeltaLogT qp qpp d e a t < gapDeltaLogT qp qpp d e a (t+1) := by
  have b1 : gapDelta qp qpp a d e t = gapDeltaLogT qp qpp d e a t :=
    gapDelta_eq_gapDeltaLogT hqp hqpp hd he ht1 (by linarith)
  have b2 : gapDelta qp qpp a d e (t+1) = gapDeltaLogT qp qpp d e a (t+1) :=
    gapDelta_eq_gapDeltaLogT hqp hqpp hd he (by linarith) (by linarith)
  rw [← b1, ← b2]
  exact gapDelta_strictly_increasing hqp hqpp hd he ht1 ht2

/-- At `t = m−1`, `a = 2m`, the general log form is `gapDeltaLog`
(the C26 duality's form). -/
theorem gapDeltaLogT_eq_gapDeltaLog {m qp qpp d dn : ℝ} :
    gapDeltaLogT qp qpp d dn (2*m) (m-1) = gapDeltaLog qp qpp d dn m := by
  unfold gapDeltaLogT gapDeltaLog
  rw [show (m:ℝ) - 1 + 1 = m by ring]

/-! ## Argmin bookkeeping (domain-general) -/

/-- If `g` is strictly decreasing on `{1, …, p−1}` and `tstar` minimizes `g`
on `{1, …, N}` (with `p ≤ N`), then `tstar ≥ p`. -/
theorem argmin_ge_of_dec (g : ℕ → ℝ) (N p tstar : ℕ)
    (hp1 : 1 ≤ p) (hpm : p ≤ N)
    (hdom : 1 ≤ tstar ∧ tstar ≤ N)
    (harg : ∀ t : ℕ, 1 ≤ t → t ≤ N → g tstar ≤ g t)
    (hdec : ∀ t : ℕ, 1 ≤ t → t < p → g (t + 1) < g t) :
    p ≤ tstar := by
  by_contra hlt
  push Not at hlt
  have key : ∀ u : ℕ, 1 ≤ u → u ≤ p - tstar → g p < g (p - u) := by
    intro u
    induction u with
    | zero => intro h1 _; omega
    | succ u ih =>
      intro hu1 hle
      have ht1 : 1 ≤ p - (u + 1) := by omega
      have htp : p - (u + 1) < p := by omega
      have hstep := hdec (p - (u + 1)) ht1 htp
      have e1 : p - (u + 1) + 1 = p - u := by omega
      rw [e1] at hstep
      by_cases hu0 : u = 0
      · subst hu0
        simpa using hstep
      · have ih' := ih (by omega) (by omega)
        exact lt_trans ih' hstep
  have hult : 1 ≤ p - tstar := by omega
  have hkle := key (p - tstar) hult le_rfl
  have e2 : p - (p - tstar) = tstar := by omega
  rw [e2] at hkle
  have hargp := harg p hp1 hpm
  linarith

/-- If `g` is strictly increasing on `{p, …, N−1}` and `tstar` minimizes `g`
on `{1, …, N}` (with `p ≤ N−1`), then `tstar ≤ p`. -/
theorem argmin_le_of_inc (g : ℕ → ℝ) (N p tstar : ℕ)
    (hpm : p ≤ N - 1) (hp1 : 1 ≤ p)
    (hdom : 1 ≤ tstar ∧ tstar ≤ N)
    (harg : ∀ t : ℕ, 1 ≤ t → t ≤ N → g tstar ≤ g t)
    (hinc : ∀ t : ℕ, p ≤ t → t ≤ N - 1 → g t < g (t + 1)) :
    tstar ≤ p := by
  by_contra hlt
  push Not at hlt
  have key : ∀ u : ℕ, 1 ≤ u → u ≤ tstar - p → g (p + u) > g p := by
    intro u
    induction u with
    | zero => intro h1 _; omega
    | succ u ih =>
      intro hu1 hle
      have h1 : p ≤ p + u := by omega
      have h2 : p + u ≤ N - 1 := by omega
      have hstep := hinc (p + u) h1 h2
      by_cases hu0 : u = 0
      · subst hu0
        simpa using hstep
      · have ih' := ih (by omega) (by omega)
        have e : p + (u + 1) = p + u + 1 := by omega
        rw [e]
        exact lt_trans ih' hstep
  have hult : 1 ≤ tstar - p := by omega
  have hkle := key (tstar - p) hult le_rfl
  have e2 : p + (tstar - p) = tstar := by omega
  rw [e2] at hkle
  have hargp := harg p hp1 (by omega)
  linarith

/-! ## The unconditional Δ-sign core (C22 Thm 2 / C25(a) shape)

At general index `t` with `c := a−t−1 ≥ t+2`: the exact criterion gives
`Δ(t) < 0` from sinh superlinearity (`sinh_scaling_gt`) plus the ratio
`q′·c/Q_{t+1} ≥ 1` (from `q″ ≤ q′`). Zero Diophantine input. -/

/-- General unconditional negative-sign core: `Δ(t) < 0` in log form,
from `x(t+1) > c·δ′`, `sinh` superlinearity, and `q′·c ≥ Q_{t+1}`. -/
theorem delta_neg_gen {qp qpp d dn a t : ℝ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hqpp_le : qpp ≤ qp)
    (ht1 : 1 ≤ t) (hta : t + 1 ≤ a - 1)
    (hc : t + 2 ≤ a - t - 1) :
    gapDeltaLogT qp qpp d dn a t < 0 := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hs0 : (0:ℝ) < d * Real.log 2 / 2 := by
    have := mul_pos hd hlog2; linarith
  have hz : (0:ℝ) < Real.log 2 / 2 := by linarith
  have hcrit := gap_criterion_CF (a := a) (t := t) hqp hqpp hd hdn ht1 hta
  have hQ : (0:ℝ) < gapQ qp qpp (t+1) := by
    unfold gapQ
    have h1 : (0:ℝ) ≤ (t+1) * qp := mul_nonneg (by linarith) hqp.le
    linarith [hqpp]
  have hQfrac : (0:ℝ) < qp / gapQ qp qpp (t+1) := div_pos hqp hQ
  -- x(t+1) = (a−t−1)·δ′ + δ_n > (a−t−1)·δ′
  have h1 : (a-t-1) * (d * Real.log 2 / 2)
      < gapx a d dn (t+1) * Real.log 2 / 2 := by
    have e1 : gapx a d dn (t+1) = (a-t-1)*d + dn := by unfold gapx; ring
    rw [e1]
    have e_lhs : (a-t-1) * (d * Real.log 2 / 2) = ((a-t-1)*d) * (Real.log 2 / 2) := by ring
    have e_rhs : ((a-t-1)*d + dn) * Real.log 2 / 2 = (((a-t-1)*d) + dn) * (Real.log 2 / 2) := by ring
    rw [e_lhs, e_rhs]
    apply mul_lt_mul_of_pos_right _ hz
    linarith [hdn]
  have h2 : Real.sinh ((a-t-1) * (d * Real.log 2 / 2))
      < Real.sinh (gapx a d dn (t+1) * Real.log 2 / 2) :=
    Real.sinh_strictMono h1
  have h3 : (a-t-1) * Real.sinh (d * Real.log 2 / 2)
      < Real.sinh ((a-t-1) * (d * Real.log 2 / 2)) :=
    sinh_scaling_gt (by linarith) hs0
  -- ratio q′·(a−t−1)/Q_{t+1} ≥ 1
  have hQP : gapQ qp qpp (t+1) ≤ qp * (a-t-1) := by
    unfold gapQ
    have hle : t + 2 ≤ a - t - 1 := hc
    have h1 : (t+1) * qp + qpp ≤ (t+2) * qp := by
      have : (t+1) * qp + qpp ≤ (t+1) * qp + qp := by linarith [hqpp_le]
      linarith [this]
    have h2 : (t+2) * qp ≤ (a-t-1) * qp :=
      mul_le_mul_of_nonneg_right (by linarith) hqp.le
    have h3 : (a-t-1) * qp = qp * (a-t-1) := by ring
    linarith [h1, h2, h3]
  have hmul : (1:ℝ) ≤ (qp / gapQ qp qpp (t+1)) * (a-t-1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hQ, one_mul]
    exact hQP
  have h5 : (a-t-1) * Real.sinh (d * Real.log 2 / 2)
      < Real.sinh (gapx a d dn (t+1) * Real.log 2 / 2) :=
    lt_trans h3 h2
  have key : Real.sinh (d * Real.log 2 / 2)
      < (qp / gapQ qp qpp (t+1)) * Real.sinh (gapx a d dn (t+1) * Real.log 2 / 2) := by
    calc Real.sinh (d * Real.log 2 / 2)
        = 1 * Real.sinh (d * Real.log 2 / 2) := (one_mul _).symm
      _ ≤ ((qp / gapQ qp qpp (t+1)) * (a-t-1)) * Real.sinh (d * Real.log 2 / 2) :=
          mul_le_mul_of_nonneg_right hmul (le_of_lt (Real.sinh_pos_iff.mpr hs0))
      _ = (qp / gapQ qp qpp (t+1)) * ((a-t-1) * Real.sinh (d * Real.log 2 / 2)) := by ring
      _ < (qp / gapQ qp qpp (t+1)) * Real.sinh (gapx a d dn (t+1) * Real.log 2 / 2) :=
          mul_lt_mul_of_pos_left h5 hQfrac
  exact hcrit.mpr key

/-- C25(a) Δ-sign core (`c25_proofs_r33.md` Theorem 1): at `t ≤ m−2`,
`a = 2m`, `Δ(t) < 0`. -/
theorem c25a_delta_neg {m : ℕ} {qp qpp d dn t : ℝ}
    (hm : 3 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hqpp_le : qpp ≤ qp)
    (ht1 : 1 ≤ t) (ht2 : t ≤ (m:ℝ) - 2) :
    gapDeltaLogT qp qpp d dn (2*(m:ℝ)) t < 0 :=
  delta_neg_gen hqp hqpp hd hdn hqpp_le ht1 (by linarith) (by linarith)

/-- C22 Δ-sign core (`c22_proofs_r24.md` Theorem 2): at `t ≤ m−1`,
`a = 2m+1`, `Δ(t) < 0`. -/
theorem c22_delta_neg {m : ℕ} {qp qpp d dn t : ℝ}
    (hm : 1 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hqpp_le : qpp ≤ qp)
    (ht1 : 1 ≤ t) (ht2 : t ≤ (m:ℝ) - 1) :
    gapDeltaLogT qp qpp d dn (2*(m:ℝ)+1) t < 0 :=
  delta_neg_gen hqp hqpp hd hdn hqpp_le ht1 (by linarith) (by linarith)

/-! ## C25(a) and C22 lower bound, assembled -/

/-- **C25(a)** (`c25_proofs_r33.md` Theorem 1): on a from-above block with
even `a = 2m ≥ 6`, `t* ≥ m−1` unconditionally — zero Diophantine input.
The variable identifications and the `Δ` bridge are explicit hypotheses. -/
theorem c25a {g : ℕ → ℝ} {tstar m : ℕ} {qp qpp d dn : ℝ}
    (hm : 3 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hqpp_le : qpp ≤ qp)
    (hdom : 1 ≤ tstar ∧ tstar ≤ 2*m - 1)
    (harg : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m - 1 → g tstar ≤ g t)
    (hdelta : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m - 2
      → g (t+1) - g t = gapDeltaLogT qp qpp d dn (2*(m:ℝ)) (t:ℝ)) :
    m - 1 ≤ tstar := by
  have hdec : ∀ t : ℕ, 1 ≤ t → t < m - 1 → g (t + 1) < g t := by
    intro t ht1 htp
    have htle : t ≤ 2*m - 2 := by omega
    have hle_nat : t ≤ m - 2 := by omega
    have htm : (t:ℝ) ≤ (m:ℝ) - 2 := by
      have h1 : (t:ℝ) ≤ ((m - 2 : ℕ):ℝ) := by exact_mod_cast hle_nat
      have h2 : ((m - 2 : ℕ):ℝ) = (m:ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ m)]
        simp
      rw [h2] at h1
      exact h1
    have ht1' : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
    have hsign := c25a_delta_neg hm hqp hqpp hd hdn hqpp_le ht1' htm
    have hbr := hdelta t ht1 htle
    linarith
  exact argmin_ge_of_dec g (2*m-1) (m-1) tstar (by omega) (by omega) hdom harg hdec

/-- **C22 lower bound** (`c22_proofs_r24.md` Theorem 2): on a from-above
block with odd `a = 2m+1 ≥ 3`, `t* ≥ m` unconditionally. -/
theorem c22_lower {g : ℕ → ℝ} {tstar m : ℕ} {qp qpp d dn : ℝ}
    (hm : 1 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hqpp_le : qpp ≤ qp)
    (hdom : 1 ≤ tstar ∧ tstar ≤ 2*m)
    (harg : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m → g tstar ≤ g t)
    (hdelta : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m - 1
      → g (t+1) - g t = gapDeltaLogT qp qpp d dn (2*(m:ℝ)+1) (t:ℝ)) :
    m ≤ tstar := by
  have hdec : ∀ t : ℕ, 1 ≤ t → t < m → g (t + 1) < g t := by
    intro t ht1 htp
    have htle : t ≤ 2*m - 1 := by omega
    have hle_nat : t ≤ m - 1 := by omega
    have htm : (t:ℝ) ≤ (m:ℝ) - 1 := by
      have h1 : (t:ℝ) ≤ ((m - 1 : ℕ):ℝ) := by exact_mod_cast hle_nat
      have h2 : ((m - 1 : ℕ):ℝ) = (m:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ m)]
        simp
      rw [h2] at h1
      exact h1
    have ht1' : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
    have hsign := c22_delta_neg hm hqp hqpp hd hdn hqpp_le ht1' htm
    have hbr := hdelta t ht1 htle
    linarith
  exact argmin_ge_of_dec g (2*m) m tstar (by omega) (by omega) hdom harg hdec

/-! ## C25(b): the checkable upper bound

`c25_proofs_r33.md` Theorem 2: `Δ(t) > 0` for `t ≥ m` under the explicit
`q′² ≥ (ln2)²(m+1)/96`, via sub-lemma E (`gap_sinh_le_mul_exp`), the
`(L2)` error-formula bound `δ′ < 1/(2mq′)` (from `delta'_formula`'s shape),
and `ln(1+x) ≥ x/(1+x)` (`gap_log_one_add_ge`). -/

/-- C25(b) Δ-sign core: at `t ≥ m`, `a = 2m`, under
`q′² ≥ (ln2)²(m+1)/96`, `Δ(t) > 0` in log form. -/
theorem c25b_delta_pos {m : ℕ} {qp qpp d dn rho r t : ℝ}
    (hm : 2 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hr : 0 ≤ r) (hrho : 0 < rho) (hrho1 : rho < 1)
    (hdn_eq : dn = rho * d) (hqpp_eq : qpp = r * qp)
    (hdelta' : d = 1 / (qp * (2*(m:ℝ) + r + rho)))
    (hcond : (Real.log 2)^2 * ((m:ℝ)+1) / 96 ≤ qp^2)
    (htm : (m:ℝ) ≤ t) (ht2 : t ≤ 2*(m:ℝ) - 2) :
    0 < gapDeltaLogT qp qpp d dn (2*(m:ℝ)) t := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hz : (0:ℝ) < Real.log 2 / 2 := by linarith
  have hs0 : (0:ℝ) < d * Real.log 2 / 2 := by
    have := mul_pos hd hlog2; linarith
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1pos : (0:ℝ) < (m:ℝ)+1 := by linarith
  -- criterion setup
  have hQ : qp < gapQ qp qpp (t+1) := by
    unfold gapQ
    have h1 : (0:ℝ) ≤ (t+1-1) * qp := mul_nonneg (by linarith) hqp.le
    linarith [hqpp]
  have hQpos : (0:ℝ) < gapQ qp qpp (t+1) := lt_trans hqp hQ
  have hv : d < gapx (2*(m:ℝ)) d dn (t+1) := by
    unfold gapx
    have h1 : (0:ℝ) ≤ (2*(m:ℝ)-(t+1)-1) * d := mul_nonneg (by linarith) hd.le
    linarith [hdn]
  have hgt := gap_delta_sign_gt (gapQ qp qpp (t+1)) qp (gapx (2*(m:ℝ)) d dn (t+1)) d
    hqp hQ hd hv
  -- λ := x(t+1)/δ′ = (2m−t−1) + ρ, with λ < m
  set lam : ℝ := (2*(m:ℝ) - t - 1) + rho with hlamdef
  have hlam_lt : lam < (m:ℝ) := by
    rw [hlamdef]; linarith [htm, hrho1]
  have hlam_pos : (0:ℝ) < lam := by
    rw [hlamdef]; linarith [ht2, hrho]
  have ex : gapx (2*(m:ℝ)) d dn (t+1) = lam * d := by
    unfold gapx; rw [hlamdef, hdn_eq]; ring
  have earg : gapx (2*(m:ℝ)) d dn (t+1) * Real.log 2 / 2
      = lam * (d * Real.log 2 / 2) := by
    rw [ex]; ring
  -- (L2): δ′ < 1/(2mq′)
  have hpos1 : (0:ℝ) < qp * (2*(m:ℝ)) := by positivity
  have hlt : qp * (2*(m:ℝ)) < qp * (2*(m:ℝ) + r + rho) := by
    apply mul_lt_mul_of_pos_left _ hqp
    linarith [hr, hrho]
  have hd_bound : d < 1 / (2*(m:ℝ)*qp) := by
    rw [hdelta', show (2:ℝ)*(m:ℝ)*qp = qp * (2*(m:ℝ)) by ring]
    exact one_div_lt_one_div_of_lt hpos1 hlt
  -- λ·s₀ < ln2/(4q′)
  have hlam_s0 : lam * (d * Real.log 2 / 2) < Real.log 2 / (4*qp) := by
    have e1 : lam * (d * Real.log 2 / 2) < (m:ℝ) * (d * Real.log 2 / 2) :=
      mul_lt_mul_of_pos_right hlam_lt hs0
    have e2 : (m:ℝ) * (d * Real.log 2 / 2)
        < (m:ℝ) * ((1/(2*(m:ℝ)*qp)) * Real.log 2 / 2) := by
      apply mul_lt_mul_of_pos_left _ hmpos
      have hstep : d * (Real.log 2 / 2) < (1/(2*(m:ℝ)*qp)) * (Real.log 2 / 2) :=
        mul_lt_mul_of_pos_right hd_bound hz
      have f1 : d * Real.log 2 / 2 = d * (Real.log 2 / 2) := by ring
      have f2 : (1/(2*(m:ℝ)*qp)) * Real.log 2 / 2 = (1/(2*(m:ℝ)*qp)) * (Real.log 2 / 2) := by ring
      rw [f1, f2]
      exact hstep
    have e3 : (m:ℝ) * ((1/(2*(m:ℝ)*qp)) * Real.log 2 / 2) = Real.log 2 / (4*qp) := by
      have hne1 : (m:ℝ) ≠ 0 := ne_of_gt hmpos
      have hne2 : qp ≠ 0 := ne_of_gt hqp
      field_simp
      ring
    rw [e3] at e2
    exact lt_trans e1 e2
  -- exp((λs₀)²/6) ≤ 1 + 1/m
  have hnn : (0:ℝ) ≤ lam * (d * Real.log 2 / 2) := mul_nonneg hlam_pos.le hs0.le
  have hnn2 : (0:ℝ) ≤ Real.log 2/(4*qp) := by positivity
  have hsq : (lam * (d * Real.log 2 / 2))^2/6 < (Real.log 2)^2/(96*qp^2) := by
    have hsq2 : (lam * (d * Real.log 2 / 2))^2 < (Real.log 2/(4*qp))^2 := by
      have hpos : (0:ℝ) < (Real.log 2/(4*qp) - lam*(d*Real.log 2/2))
          * (Real.log 2/(4*qp) + lam*(d*Real.log 2/2)) :=
        mul_pos (by linarith) (by linarith)
      nlinarith [hpos]
    have e4 : (Real.log 2/(4*qp))^2 = ((Real.log 2)^2/(96*qp^2)) * 6 := by
      have hne : qp ≠ 0 := ne_of_gt hqp
      field_simp
      ring
    rw [e4] at hsq2
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 6)]
    exact hsq2
  have hln : (Real.log 2)^2/(96*qp^2) ≤ Real.log (1 + 1/(m:ℝ)) := by
    have h1m : (0:ℝ) < 1/(m:ℝ) := by positivity
    have hge := gap_log_one_add_ge (1/(m:ℝ)) h1m
    have hne : (m:ℝ) ≠ 0 := ne_of_gt hmpos
    have e5 : (1/(m:ℝ))/(1+1/(m:ℝ)) = 1/((m:ℝ)+1) := by
      field_simp
    have hge2 := hge
    rw [e5] at hge2
    have h6 : (Real.log 2)^2/(96*qp^2) ≤ 1/((m:ℝ)+1) := by
      have hqp2 : (0:ℝ) < 96*qp^2 := by positivity
      rw [le_div_iff₀ hm1pos, div_mul_eq_mul_div, div_le_iff₀ hqp2, one_mul]
      have hcond2 : (Real.log 2)^2 * ((m:ℝ)+1) ≤ 96*qp^2 := by
        have hcc := hcond
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 96)] at hcc
        linarith [hcc]
      have e : (Real.log 2)^2 * ((m:ℝ)+1) = (Real.log 2)^2 * ((m:ℝ)+1) := rfl
      linarith [hcond2]
    exact le_trans h6 hge2
  have hexp_bound : Real.exp ((lam * (d * Real.log 2 / 2))^2/6) ≤ 1 + 1/(m:ℝ) := by
    have h1p : (0:ℝ) < 1 + 1/(m:ℝ) := by positivity
    have hle := Real.exp_le_exp.mpr (le_trans (le_of_lt hsq) hln)
    rwa [Real.exp_log h1p] at hle
  -- q′/Q_{t+1} ≤ 1/(m+1)
  have hqppnn : (0:ℝ) ≤ qpp := by rw [hqpp_eq]; positivity
  have hQge : ((m:ℝ)+1)*qp ≤ gapQ qp qpp (t+1) := by
    unfold gapQ
    have h1 : ((m:ℝ)+1)*qp ≤ (t+1)*qp :=
      mul_le_mul_of_nonneg_right (by linarith) hqp.le
    linarith [h1, hqppnn]
  have hQfrac : qp / gapQ qp qpp (t+1) ≤ 1/((m:ℝ)+1) := by
    rw [le_div_iff₀ hm1pos, div_mul_eq_mul_div, div_le_iff₀ hQpos, one_mul]
    have e : qp * ((m:ℝ)+1) = ((m:ℝ)+1)*qp := by ring
    rw [e]; exact hQge
  -- main estimate
  have hup := gap_sinh_le_mul_exp (lam * (d * Real.log 2 / 2))
    (mul_nonneg hlam_pos.le hs0.le)
  have hlow := sinh_ge_id hs0.le
  have hcoeff : (qp / gapQ qp qpp (t+1)) * lam
      * Real.exp ((lam * (d * Real.log 2 / 2))^2/6) < 1 := by
    have epos1 : (0:ℝ) ≤ Real.exp ((lam * (d * Real.log 2 / 2))^2/6) :=
      (Real.exp_pos _).le
    have epos2 : (0:ℝ) < 1/((m:ℝ)+1) := by positivity
    calc (qp / gapQ qp qpp (t+1)) * lam * Real.exp ((lam * (d * Real.log 2 / 2))^2/6)
        ≤ (1/((m:ℝ)+1)) * lam * Real.exp ((lam * (d * Real.log 2 / 2))^2/6) := by
          apply mul_le_mul_of_nonneg_right _ epos1
          exact mul_le_mul_of_nonneg_right hQfrac hlam_pos.le
      _ < (1/((m:ℝ)+1)) * (m:ℝ) * Real.exp ((lam * (d * Real.log 2 / 2))^2/6) := by
          apply mul_lt_mul_of_pos_right _ (by positivity)
          exact mul_lt_mul_of_pos_left hlam_lt epos2
      _ ≤ (1/((m:ℝ)+1)) * (m:ℝ) * (1 + 1/(m:ℝ)) := by
          apply mul_le_mul_of_nonneg_left hexp_bound (by positivity)
      _ = 1 := by
          have hne1 : ((m:ℝ)+1) ≠ 0 := ne_of_gt hm1pos
          have hne2 : (m:ℝ) ≠ 0 := ne_of_gt hmpos
          field_simp
  have hmain : (qp / gapQ qp qpp (t+1)) * Real.sinh (lam * (d * Real.log 2 / 2))
      < Real.sinh (d * Real.log 2 / 2) := by
    have hQnn : (0:ℝ) ≤ qp / gapQ qp qpp (t+1) := le_of_lt (div_pos hqp hQpos)
    calc (qp / gapQ qp qpp (t+1)) * Real.sinh (lam * (d * Real.log 2 / 2))
        ≤ (qp / gapQ qp qpp (t+1))
          * ((lam * (d * Real.log 2 / 2)) * Real.exp ((lam * (d * Real.log 2 / 2))^2/6)) :=
          mul_le_mul_of_nonneg_left hup hQnn
      _ = ((qp / gapQ qp qpp (t+1)) * lam * Real.exp ((lam * (d * Real.log 2 / 2))^2/6))
          * (d * Real.log 2 / 2) := by ring
      _ < 1 * (d * Real.log 2 / 2) := mul_lt_mul_of_pos_right hcoeff hs0
      _ = d * Real.log 2 / 2 := one_mul _
      _ ≤ Real.sinh (d * Real.log 2 / 2) := hlow
  apply hgt.mpr
  rw [earg]
  exact hmain

/-- **C25(b)** (`c25_proofs_r33.md` Theorem 2): on a from-above block with
even `a = 2m ≥ 4`, if `q′² ≥ (ln2)²(m+1)/96` then `t* ≤ m`. -/
theorem c25b {g : ℕ → ℝ} {tstar m : ℕ} {qp qpp d dn rho r : ℝ}
    (hm : 2 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hr : 0 ≤ r) (hrho : 0 < rho) (hrho1 : rho < 1)
    (hdn_eq : dn = rho * d) (hqpp_eq : qpp = r * qp)
    (hdelta' : d = 1 / (qp * (2*(m:ℝ) + r + rho)))
    (hcond : (Real.log 2)^2 * ((m:ℝ)+1) / 96 ≤ qp^2)
    (hdom : 1 ≤ tstar ∧ tstar ≤ 2*m - 1)
    (harg : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m - 1 → g tstar ≤ g t)
    (hdelta : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m - 2
      → g (t+1) - g t = gapDeltaLogT qp qpp d dn (2*(m:ℝ)) (t:ℝ)) :
    tstar ≤ m := by
  have hinc : ∀ t : ℕ, m ≤ t → t ≤ 2*m - 2 → g t < g (t + 1) := by
    intro t htm htle
    have htm' : (m:ℝ) ≤ (t:ℝ) := by exact_mod_cast htm
    have hle_nat : t ≤ 2*m - 2 := htle
    have ht2' : (t:ℝ) ≤ 2*(m:ℝ) - 2 := by
      have h1 : (t:ℝ) ≤ ((2*m - 2 : ℕ):ℝ) := by exact_mod_cast hle_nat
      have h2 : ((2*m - 2 : ℕ):ℝ) = 2*(m:ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ 2*m)]
        push_cast
        ring
      rw [h2] at h1
      exact h1
    have hsign := c25b_delta_pos hm hqp hqpp hd hdn hr hrho hrho1 hdn_eq hqpp_eq
      hdelta' hcond htm' ht2'
    have hbr := hdelta t (by omega) htle
    linarith
  exact argmin_le_of_inc g (2*m-1) m tstar (by omega) (by omega) hdom harg hinc

/-! ## Monotonicity chains from a single sign -/

/-- From `Δ > 0` at base index `b`, strict increase gives `Δ > 0`
at every later index in range. -/
theorem gapDeltaLogT_pos_chain {qp qpp d dn : ℝ} {a : ℝ} {b t : ℕ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hb1 : 1 ≤ b)
    (hbase : (0:ℝ) < gapDeltaLogT qp qpp d dn a (b:ℝ))
    (htm : b ≤ t) (hta : (t:ℝ) ≤ a - 2) :
    (0:ℝ) < gapDeltaLogT qp qpp d dn a (t:ℝ) := by
  -- R101: explicit induction on the distance n = t - b, with gapDeltaLogT_mono's
  -- index pinned (the R97 IsOrderedRing ?m blocker came from unpinned implicits).
  have key : ∀ n : ℕ, ((b + n : ℕ):ℝ) ≤ a - 2 →
      0 < gapDeltaLogT qp qpp d dn a ((b + n : ℕ):ℝ) := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa using hbase
    | succ n ih =>
      intro hn
      have e : ((b + (n + 1) : ℕ):ℝ) = ((b + n : ℕ):ℝ) + 1 := by
        push_cast; ring
      have hnn : ((b + n : ℕ):ℝ) ≤ a - 2 := by linarith
      have ih' := ih hnn
      have h1 : (1:ℝ) ≤ ((b + n : ℕ):ℝ) := by
        have hbn : 1 ≤ b + n := by omega
        exact_mod_cast hbn
      have h2 : ((b + n : ℕ):ℝ) ≤ a - 3 := by linarith
      have hmono := gapDeltaLogT_mono (t := ((b + n : ℕ):ℝ)) hqp hqpp hd hdn h1 h2
      rw [e]
      linarith
  have htb : b + (t - b) = t := by omega
  have hbound : ((b + (t - b) : ℕ):ℝ) ≤ a - 2 := by
    rw [htb]; exact hta
  have hfin := key (t - b) hbound
  rw [htb] at hfin
  exact hfin
/-- From `Δ < 0` at base index `b`, strict increase gives `Δ < 0`
at every earlier index in range. -/
theorem gapDeltaLogT_neg_chain {qp qpp d dn : ℝ} {a : ℝ} {b t : ℕ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hbase : gapDeltaLogT qp qpp d dn a (b:ℝ) < 0)
    (hba : (b:ℝ) ≤ a - 2)
    (ht1 : 1 ≤ t) (htm : t ≤ b) :
    gapDeltaLogT qp qpp d dn a (t:ℝ) < 0 := by
  -- R101: induction on d_ with a varying base u (u + d_ = b); mono at u steps down.
  have key : ∀ d_ u : ℕ, 1 ≤ u → u + d_ = b →
      gapDeltaLogT qp qpp d dn a (u:ℝ) < 0 := by
    intro d_
    induction d_ with
    | zero =>
      intro u _ h
      have hub : u = b := by omega
      rw [hub]; exact hbase
    | succ d_ ih =>
      intro u hu h
      have h1 : (1:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu
      have h2 : (u:ℝ) ≤ a - 3 := by
        have hub : ((u + (d_ + 1) : ℕ):ℝ) = (b:ℝ) := by exact_mod_cast h
        have hcast : ((u + (d_ + 1) : ℕ):ℝ) = (u:ℝ) + ((d_:ℝ) + 1) := by
          push_cast; ring
        rw [hcast] at hub
        have hnn : (0:ℝ) ≤ (d_:ℝ) := Nat.cast_nonneg _
        linarith
      have hmono := gapDeltaLogT_mono (t := (u:ℝ)) hqp hqpp hd hdn h1 h2
      have hstep : (u + 1) + d_ = b := by omega
      have hu1 : 1 ≤ u + 1 := by omega
      have ih' := ih (u + 1) hu1 hstep
      have e : ((u + 1 : ℕ):ℝ) = (u:ℝ) + 1 := by push_cast; ring
      rw [e] at ih'
      linarith
  exact key (b - t) t ht1 (by omega)
/-! ## C26 corollaries a/b/c -/

/-- **C26a** (`c26_proofs_r36.md` Corollary C26a): `M⁻ < M⁺` implies
`t* = m−1`, unconditionally — the duality gives `Δ(m−1) > 0`, the
increasing chain gives `t* ≤ m−1`, and C25(a) gives `t* ≥ m−1`. -/
theorem c26a {g : ℕ → ℝ} {tstar m : ℕ} {qp qpp d dn : ℝ}
    (hm : 3 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hqpp_le : qpp ≤ qp)
    (hM : gapMminus qp qpp (d*Real.log 2/2) m (dn/d)
      < gapMplus qp qpp (d*Real.log 2/2) m (dn/d))
    (hdom : 1 ≤ tstar ∧ tstar ≤ 2*m - 1)
    (harg : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m - 1 → g tstar ≤ g t)
    (hdelta : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m - 2
      → g (t+1) - g t = gapDeltaLogT qp qpp d dn (2*(m:ℝ)) (t:ℝ)) :
    tstar = m - 1 := by
  have hmR : (3:ℝ) ≤ (m:ℝ) := by have h3 : (3:ℕ) ≤ m := hm; exact_mod_cast h3
  have hlb := c25a hm hqp hqpp hd hdn hqpp_le hdom harg hdelta
  have hdual := (gap_margin_duality hmR hqp hqpp hd hdn).1.mp hM
  rw [← gapDeltaLogT_eq_gapDeltaLog] at hdual
  have ecast : ((m-1 : ℕ):ℝ) = (m:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; simp
  have hbase : (0:ℝ) < gapDeltaLogT qp qpp d dn (2*(m:ℝ)) ((m-1 : ℕ):ℝ) := by
    rw [ecast]; exact hdual
  have hinc : ∀ t : ℕ, m - 1 ≤ t → t ≤ 2*m - 2 → g t < g (t + 1) := by
    intro t htm htle
    have hle_nat : t ≤ 2*m - 2 := htle
    have hta : (t:ℝ) ≤ 2*(m:ℝ) - 2 := by
      have h1 : (t:ℝ) ≤ ((2*m - 2 : ℕ):ℝ) := by exact_mod_cast hle_nat
      have h2 : ((2*m - 2 : ℕ):ℝ) = 2*(m:ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ 2*m)]
        push_cast
        ring
      rw [h2] at h1
      exact h1
    have hpos := gapDeltaLogT_pos_chain hqp hqpp hd hdn (b := m-1)
      (a := 2*(m:ℝ)) (by omega) hbase htm hta
    have hbr := hdelta t (by omega) htle
    linarith
  have hub := argmin_le_of_inc g (2*m-1) (m-1) tstar (by omega) (by omega) hdom harg hinc
  omega

/-- **C26b** (`c26_proofs_r36.md` Corollary C26b): `M⁻ > M⁺` plus C25(b)'s
checkable hypothesis implies `t* = m` — the duality gives `Δ(m−1) < 0`,
the decreasing chain gives `t* ≥ m`, and C25(b) gives `t* ≤ m`. -/
theorem c26b {g : ℕ → ℝ} {tstar m : ℕ} {qp qpp d dn rho r : ℝ}
    (hm : 3 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hr : 0 ≤ r) (hrho : 0 < rho) (hrho1 : rho < 1)
    (hdn_eq : dn = rho * d) (hqpp_eq : qpp = r * qp)
    (hdelta' : d = 1 / (qp * (2*(m:ℝ) + r + rho)))
    (hcond : (Real.log 2)^2 * ((m:ℝ)+1) / 96 ≤ qp^2)
    (hM : gapMplus qp qpp (d*Real.log 2/2) m (dn/d)
      < gapMminus qp qpp (d*Real.log 2/2) m (dn/d))
    (hdom : 1 ≤ tstar ∧ tstar ≤ 2*m - 1)
    (harg : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m - 1 → g tstar ≤ g t)
    (hdelta : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m - 2
      → g (t+1) - g t = gapDeltaLogT qp qpp d dn (2*(m:ℝ)) (t:ℝ)) :
    tstar = m := by
  have hmR : (3:ℝ) ≤ (m:ℝ) := by have h3 : (3:ℕ) ≤ m := hm; exact_mod_cast h3
  have hub := c25b (by omega) hqp hqpp hd hdn hr hrho hrho1 hdn_eq hqpp_eq
    hdelta' hcond hdom harg hdelta
  have hdual := (gap_margin_duality hmR hqp hqpp hd hdn).2.1.mp hM
  have ecast : ((m-1 : ℕ):ℝ) = (m:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; simp
  have hbase : gapDeltaLogT qp qpp d dn (2*(m:ℝ)) ((m-1 : ℕ):ℝ) < 0 := by
    rw [ecast, gapDeltaLogT_eq_gapDeltaLog]; exact hdual
  have hba : ((m-1 : ℕ):ℝ) ≤ 2*(m:ℝ) - 2 := by
    rw [ecast]; linarith [hmR]
  have hdec : ∀ t : ℕ, 1 ≤ t → t < m → g (t + 1) < g t := by
    intro t ht1 htp
    have hneg := gapDeltaLogT_neg_chain hqp hqpp hd hdn (b := m-1)
      (a := 2*(m:ℝ)) hbase hba ht1 (by omega)
    have hbr := hdelta t ht1 (by omega)
    linarith
  have hlb := argmin_ge_of_dec g (2*m-1) m tstar (by omega) (by omega) hdom harg hdec
  omega

/-- **C26c** (`c26_proofs_r36.md` Corollary C26c, the selector in disguise):
under C25(b)'s hypothesis (and C23(b)'s `K(n)` for the `ρ < r` direction),
`M⁻ < M⁺ → ρ < r` and `M⁻ > M⁺ → ρ > r` — the margin order IS the C23
selector. Uses `c26a`/`c26b` for the argmin readings, `c23a`/`c23b` for the
selector, and `cf_selector_ne` (ρ≠r always) to close the trichotomy. -/
theorem c26c {g : ℕ → ℝ} {tstar m : ℕ} {qp qpp d dn rho r : ℝ} {α : ℝ} {n : ℕ}
    (hirr : Irrational α)
    (hrho_cf : rho = |cerr α (n+2)| / |cerr α (n+1)|)
    (hr_cf : r = Q α n / Q α (n+1))
    (hm : 3 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hqpp_le : qpp ≤ qp)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hdn_eq : dn = rho * d) (hqpp_eq : qpp = r * qp)
    (hdelta' : d = 1 / (qp * (2*(m:ℝ) + r + rho)))
    (hcond : (Real.log 2)^2 * ((m:ℝ)+1) / 96 ≤ qp^2)
    (hK : 3 * (Real.log 2)^2 / 128 * ((m:ℝ) + 1) ≤ qp^2 * (r - rho))
    (hdom : 1 ≤ tstar ∧ tstar ≤ 2*m - 1)
    (harg : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m - 1 → g tstar ≤ g t)
    (hdelta : ∀ t : ℕ, 1 ≤ t → t ≤ 2*m - 2
      → g (t+1) - g t = gapDeltaLogT qp qpp d dn (2*(m:ℝ)) (t:ℝ)) :
    (gapMminus qp qpp (d*Real.log 2/2) m (dn/d) < gapMplus qp qpp (d*Real.log 2/2) m (dn/d)
      → rho < r)
    ∧ (gapMplus qp qpp (d*Real.log 2/2) m (dn/d) < gapMminus qp qpp (d*Real.log 2/2) m (dn/d)
      → r < rho) := by
  have hrpos : (0:ℝ) < r := by
    by_contra hcon
    push Not at hcon
    have hle := mul_nonpos_of_nonpos_of_nonneg hcon hqp.le
    rw [← hqpp_eq] at hle
    linarith [hqpp]
  have hne : rho ≠ r := by
    rw [hrho_cf, hr_cf]
    exact cf_selector_ne hirr n
  have harg23 : ∀ t : ℕ, t = m - 1 ∨ t = m → g tstar ≤ g t := by
    intro t ht
    cases ht with
    | inl h => rw [h]; exact harg (m-1) (by omega) (by omega)
    | inr h => rw [h]; exact harg m (by omega) (by omega)
  have hdelta23 : g m - g (m - 1) = gapDeltaLog qp qpp d dn (m : ℝ) := by
    have h1 : g ((m-1)+1) - g (m-1) = gapDeltaLogT qp qpp d dn (2*(m:ℝ)) (((m-1 : ℕ)):ℝ) :=
      hdelta (m-1) (by omega) (by omega)
    have e1 : m - 1 + 1 = m := by omega
    rw [e1] at h1
    have e2 : ((m-1 : ℕ):ℝ) = (m:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]; simp
    rw [e2, gapDeltaLogT_eq_gapDeltaLog] at h1
    exact h1
  constructor
  · intro hM
    have hts := c26a hm hqp hqpp hd hdn hqpp_le hM hdom harg hdelta
    by_contra hcon
    push Not at hcon
    have hts2 := c23a (by omega) hqp hqpp hd hrho0 hrpos hcon hdn_eq hqpp_eq
      (Or.inl hts) harg23 hdelta23
    omega
  · intro hM
    have hts := c26b hm hqp hqpp hd hdn hr0 hrho0 hrho1 hdn_eq hqpp_eq
      hdelta' hcond hM hdom harg hdelta
    rcases lt_trichotomy rho r with h | h | h
    · have hts2 := c23b (by omega) hqp hqpp hd hrho0 hrho1 hrpos hr1 h hdn_eq hqpp_eq
        hdelta' hK (Or.inr hts) harg23 hdelta23
      omega
    · exact absurd h hne
    · exact h

/-! ## C22 upper bound: `Δ(m) > 0` under the explicit `L(n)` condition

`c22_proofs_r24.md` Theorem 3's upper bound goes through a general
log-inequality (`2x ≤ ln((1+x)/(1−x))`, monotone-derivative lemma), then
the C22-specific chain (Steps A–E of the hand proof). -/

/-- General log inequality: `2x ≤ ln((1+x)/(1−x))` for `0 ≤ x < 1`,
by monotonicity of `F(t) = ln((1+t)/(1−t)) − 2t` from `F(0) = 0`. -/
theorem log_one_add_div_one_sub_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    2*x ≤ Real.log ((1+x)/(1-x)) := by
  -- R101: F(t) = ln((1+t)/(1-t)) - 2t is monotone on Icc 0 x (x < 1 keeps
  -- 1-t > 0), with F(0) = 0 and F'(t) = 2t^2/(1-t^2) >= 0.
  -- Uses monotoneOn_of_hasDerivWithinAt_nonneg (this Mathlib rev has no
  -- differentiableOn_of_hasDerivAt; interior is `interior`, not Set.interior).
  have hderiv : ∀ t : ℝ, t ∈ Set.Ioo (0:ℝ) x →
      HasDerivAt (fun t => Real.log ((1+t)/(1-t)) - 2*t) (2*t^2/(1-t^2)) t := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht.1
    have htx : t < x := ht.2
    have ht1 : t < 1 := lt_trans htx hx1
    have hne1 : (1:ℝ) - t ≠ 0 := sub_ne_zero.mpr (ne_of_lt ht1).symm
    have hne2 : (1:ℝ) + t ≠ 0 := ne_of_gt (by linarith)
    have hnum : HasDerivAt (fun t => 1 + t) 1 t := (hasDerivAt_id t).const_add 1
    have hden : HasDerivAt (fun t => 1 - t) (-1) t := (hasDerivAt_id t).const_sub 1
    have hq := hnum.div hden hne1
    have hpos : (0:ℝ) < (1+t)/(1-t) := div_pos (by linarith) (by linarith)
    have hlog : HasDerivAt (fun t => Real.log ((1+t)/(1-t)))
        ((((1*(1-t) - (1+t)*(-1))/(1-t)^2) / ((1+t)/(1-t)))) t :=
      hq.log hpos.ne'
    have h2t : HasDerivAt (fun t => 2*t) 2 t := by
      have h := (hasDerivAt_id t).const_mul 2
      simpa using h
    have hsub := hlog.sub h2t
    have hder_eq : ((((1*(1-t) - (1+t)*(-1))/(1-t)^2) / ((1+t)/(1-t))) - 2)
        = 2*t^2/(1-t^2) := by
      have hne3 : ((1:ℝ)-t)^2 ≠ 0 := pow_ne_zero 2 hne1
      have hne4 : (1:ℝ) - t^2 ≠ 0 := by
        have h := mul_ne_zero hne1 hne2
        rwa [show (1 - t) * (1 + t) = 1 - t^2 by ring] at h
      have h2 : (1*(1-t) - (1+t)*(-1))/(1-t)^2 = 2/(1-t)^2 := by
        congr 1; ring
      rw [h2]
      field_simp
      ring
    rw [hder_eq] at hsub
    exact hsub.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => rfl)
  have hmono : MonotoneOn (fun t => Real.log ((1+t)/(1-t)) - 2*t) (Set.Icc 0 x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Icc (0:ℝ) x)
      (convex_Icc (0:ℝ) x) (f' := fun t => 2*t^2/(1-t^2)) ?_ ?_ ?_
    · have hdiv : ContinuousOn (fun t : ℝ => (1+t)/(1-t)) (Set.Icc 0 x) := by
        refine ContinuousOn.div ?_ ?_ ?_
        · exact continuousOn_const.add continuousOn_id
        · exact continuousOn_const.sub continuousOn_id
        · intro t ht
          rw [Set.mem_Icc] at ht
          show (1:ℝ) - t ≠ 0
          have h1t : (0:ℝ) < 1 - t := by
            have htx : t ≤ x := ht.2
            linarith
          exact ne_of_gt h1t
      have hlogc : ContinuousOn (fun t : ℝ => Real.log ((1+t)/(1-t))) (Set.Icc 0 x) := by
        refine ContinuousOn.comp Real.continuousOn_log hdiv ?_
        intro t ht
        rw [Set.mem_Icc] at ht
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
        have h1t : (0:ℝ) < 1 - t := by
          have htx : t ≤ x := ht.2
          linarith
        have hpos : (0:ℝ) < (1+t)/(1-t) := by
          apply div_pos <;> linarith
        exact ne_of_gt hpos
      exact hlogc.sub ((continuous_const.mul continuous_id).continuousOn)
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      show (0:ℝ) ≤ 2*t^2/(1-t^2)
      have hx0' : (0:ℝ) < t := ht.1
      have htx : t < x := ht.2
      have ht1 : t < 1 := lt_trans htx hx1
      have h1 : (0:ℝ) ≤ 2*t^2 := by positivity
      have h2 : (0:ℝ) < 1 - t^2 := by
        have h : (1 - t) * (1 + t) > 0 := mul_pos (sub_pos.mpr ht1) (by linarith)
        have e : (1 - t) * (1 + t) = 1 - t^2 := by ring
        linarith
      exact div_nonneg h1 h2.le
  have h0 : (0:ℝ) ∈ Set.Icc 0 x := ⟨le_rfl, hx0⟩
  have hxmem : x ∈ Set.Icc 0 x := ⟨hx0, le_rfl⟩
  have h := hmono h0 hxmem hx0
  dsimp only at h
  rw [show ((1+(0:ℝ))/(1-0)) = 1 by norm_num, Real.log_one] at h
  linarith

set_option maxHeartbeats 1000000 in
/-- C22 Δ-sign core, positive direction: at `t = m`, `a = 2m+1`, under
`192·q″·q′²/((2m+2)·q′+q″) ≥ (ln2)²` (the `L(n)` condition of
`c22_proofs_r24.md` Theorem 3 — R101's corrected form; R97's
`192·q′·q″/(q′+q″)` was a mistranscription), `Δ(m) > 0` in log form.
Steps A–E. -/
theorem c22_delta_pos_at {m : ℕ} {qp qpp d dn rho r : ℝ}
    (hm : 2 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (hdn : 0 < dn)
    (hr : 0 ≤ r) (hrho : 0 < rho) (hrho1 : rho < 1)
    (hdn_eq : dn = rho * d) (hqpp_eq : qpp = r * qp)
    (hdelta' : d = 1 / (qp * (2*(m:ℝ)+1 + r + rho)))
    (hL : (Real.log 2)^2 ≤ 192 * qpp * qp^2 / ((2*(m:ℝ)+2)*qp + qpp))
    (hm3 : (3:ℝ) ≤ (m:ℝ) - 1) :
    0 < gapDeltaLogT qp qpp d dn (2*(m:ℝ)+1) (m:ℝ) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hqp_ne : qp ≠ 0 := ne_of_gt hqp
  -- Hand-proof quantities: A = δ′·Q_{m+1}, μ the Step-A excess,
  -- s = ln2/(2q′), c₀ = δ′q′, P = (1−A)s, Qc = c₀s, R the sinh ratio.
  set A : ℝ := d * (((m:ℝ)+1)*qp + qpp) with hAdef
  set mu : ℝ := (d*(qp+qpp) - qp*dn)/2 with hmudef
  set s : ℝ := Real.log 2/(2*qp) with hsdef
  set c0 : ℝ := d*qp with hc0def
  set P : ℝ := (1-A)*s with hPdef
  set Qc : ℝ := c0*s with hQcdef
  set R : ℝ := (Real.sinh P / P) / (Real.sinh Qc / Qc) with hRdef
  have hs_pos : (0:ℝ) < s := by rw [hsdef]; positivity
  have hc0_pos : (0:ℝ) < c0 := by rw [hc0def]; positivity
  have hpos : (0:ℝ) < qp * (2*(m:ℝ)+1+r+rho) := by
    apply mul_pos hqp; linarith [hr, hrho, hmpos]
  have hdq : d * (qp * (2*(m:ℝ)+1+r+rho)) = 1 := by
    rw [hdelta', div_mul_cancel₀ _ (ne_of_gt hpos)]
  -- (F1) at t = a: q′·δ_n + δ′·((2m+1)·q′+q″) = 1
  have hF1' : qp * dn + d * ((2*(m:ℝ)+1) * qp + qpp) = 1 := by
    rw [hdn_eq, hqpp_eq]
    linear_combination hdq
  -- Step A: A = 1/2 + μ with 0 < μ < 1/2
  have hA_half : A = 1/2 + mu := by
    rw [hAdef, hmudef]
    linear_combination (1/2 : ℝ) * hF1'
  have hmu_pos : (0:ℝ) < mu := by
    rw [hmudef, hdn_eq, hqpp_eq]
    have h1 : (0:ℝ) < d * qp * (1 + r - rho) := by
      apply mul_pos (mul_pos hd hqp); linarith [hr, hrho1]
    have e : d*(qp + r*qp) - qp*(rho*d) = d*qp*(1+r-rho) := by ring
    rw [e]; linarith [h1]
  have hmu_lt : mu < 1/2 := by
    rw [hmudef]
    have hqd : (0:ℝ) < qp*dn := mul_pos hqp hdn
    have hle : d*(qp+qpp) ≤ d*((2*(m:ℝ)+1)*qp+qpp) := by
      apply mul_le_mul_of_nonneg_left _ hd.le
      have h1 : (0:ℝ) ≤ 2*(m:ℝ)*qp := by
        have h2 : (0:ℝ) ≤ (m:ℝ) := le_of_lt hmpos
        have h3 : (0:ℝ) ≤ (2:ℝ)*(m:ℝ) := by linarith [h2]
        exact mul_nonneg h3 hqp.le
      linarith [h1]
    linarith [hF1', hqd, hle]
  have hA_pos : (0:ℝ) < A := by rw [hA_half]; linarith [hmu_pos]
  have hA_lt1 : A < 1 := by rw [hA_half]; linarith [hmu_lt]
  have h1mA_pos : (0:ℝ) < 1 - A := by linarith [hA_lt1]
  have h1mA_half : 1 - A = 1/2 - mu := by rw [hA_half]; ring
  have hP_pos : (0:ℝ) < P := by rw [hPdef]; exact mul_pos h1mA_pos hs_pos
  have hP_nonneg : (0:ℝ) ≤ P := le_of_lt hP_pos
  have hQc_pos : (0:ℝ) < Qc := by rw [hQcdef]; exact mul_pos hc0_pos hs_pos
  have hQc_nonneg : (0:ℝ) ≤ Qc := le_of_lt hQc_pos
  have hA_ne : A ≠ 0 := ne_of_gt hA_pos
  have h1mA_ne : (1:ℝ) - A ≠ 0 := ne_of_gt h1mA_pos
  have hc0_ne : c0 ≠ 0 := ne_of_gt hc0_pos
  have hP_ne : P ≠ 0 := ne_of_gt hP_pos
  have hQc_ne : Qc ≠ 0 := ne_of_gt hQc_pos
  have hsinhQc : (0:ℝ) < Real.sinh Qc := Real.sinh_pos_iff.mpr hQc_pos
  have hsinhQc_ne : Real.sinh Qc ≠ 0 := ne_of_gt hsinhQc
  -- Δ-sign criterion inputs at t = m
  have hQ : qp < ((m:ℝ)+1)*qp + qpp := by
    have h1 : (0:ℝ) < (m:ℝ)*qp := mul_pos hmpos hqp
    have h2 : ((m:ℝ)+1)*qp + qpp - qp = (m:ℝ)*qp + qpp := by ring
    linarith [h1, hqpp, h2]
  have hv : d < gapx (2*(m:ℝ)+1) d dn ((m:ℝ)+1) := by
    unfold gapx
    have h1 : (0:ℝ) < ((m:ℝ)-1)*d + dn := by
      have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      have h2 : (0:ℝ) ≤ ((m:ℝ)-1)*d := mul_nonneg (by linarith [hm1]) hd.le
      linarith [h2, hdn]
    have e : (2*(m:ℝ)+1-((m:ℝ)+1))*d + dn = d + (((m:ℝ)-1)*d + dn) := by ring
    rw [e]; linarith [h1]
  have hgt := gap_delta_sign_gt (((m:ℝ)+1)*qp+qpp) qp
    (gapx (2*(m:ℝ)+1) d dn ((m:ℝ)+1)) d hqp hQ hd hv
  -- Bridge identities: x(m+1) = (1−A)/q′ (F1) and q′/Q_{m+1} = c₀/A
  have hx : gapx (2*(m:ℝ)+1) d dn ((m:ℝ)+1) = (1-A)/qp := by
    rw [eq_div_iff hqp_ne, hAdef]
    unfold gapx
    linear_combination hF1'
  have hQA : qp / (((m:ℝ)+1)*qp+qpp) = c0 / A := by
    rw [hc0def, hAdef]
    have hD : ((m:ℝ)+1)*qp+qpp ≠ 0 := by
      have h1 : (0:ℝ) < ((m:ℝ)+1)*qp+qpp := by
        have h2 : (0:ℝ) < (m:ℝ)*qp := mul_pos hmpos hqp
        have e : ((m:ℝ)+1)*qp+qpp = qp + ((m:ℝ)*qp + qpp) := by ring
        rw [e]; linarith [hqp, h2, hqpp]
      exact ne_of_gt h1
    have hDd : d * (((m:ℝ)+1)*qp+qpp) ≠ 0 := by
      have h1 : (0:ℝ) < ((m:ℝ)+1)*qp+qpp := by
        have h2 : (0:ℝ) < (m:ℝ)*qp := mul_pos hmpos hqp
        have e : ((m:ℝ)+1)*qp+qpp = qp + ((m:ℝ)*qp + qpp) := by ring
        rw [e]; linarith [hqp, h2, hqpp]
      exact ne_of_gt (mul_pos hd h1)
    field_simp
  -- Step E: P²/6 < 4μ
  have hden : (0:ℝ) < (2*(m:ℝ)+2)*qp + qpp := by
    have h1 : (0:ℝ) < (m:ℝ)*qp := mul_pos hmpos hqp
    have e : (2*(m:ℝ)+2)*qp + qpp = 2*((m:ℝ)*qp) + 2*qp + qpp := by ring
    rw [e]; linarith [h1, hqp, hqpp]
  have hP_lt : P < Real.log 2/(4*qp) := by
    rw [hPdef, hsdef]
    have e : (1-A) * (Real.log 2/(2*qp)) < (1/2) * (Real.log 2/(2*qp)) :=
      mul_lt_mul_of_pos_right (by rw [h1mA_half]; linarith [hmu_pos]) hs_pos
    have e2 : (1/2:ℝ) * (Real.log 2/(2*qp)) = Real.log 2/(4*qp) := by ring
    rw [e2] at e; exact e
  have hP6 : P^2/6 < (Real.log 2)^2/(96*qp^2) := by
    have hb : (0:ℝ) < Real.log 2/(4*qp) := by positivity
    have hsq : P^2 < (Real.log 2/(4*qp))^2 := by
      have h1 : (0:ℝ) < Real.log 2/(4*qp) - P := sub_pos.mpr hP_lt
      have h2 : (0:ℝ) < Real.log 2/(4*qp) + P := by linarith [hb, hP_pos]
      have h3 := mul_pos h1 h2
      nlinarith [h3]
    have e : (Real.log 2/(4*qp))^2 = (Real.log 2)^2/(96*qp^2) * 6 := by
      have hqpne : qp ≠ 0 := hqp_ne
      field_simp
      ring
    rw [e] at hsq
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 6)]
    linarith [hsq]
  have hstep1 : (Real.log 2)^2/(96*qp^2) ≤ 2*qpp/((2*(m:ℝ)+2)*qp + qpp) := by
    have hL2 : (Real.log 2)^2 * ((2*(m:ℝ)+2)*qp + qpp) ≤ 192*qpp*qp^2 := by
      have h := hL
      rw [le_div_iff₀ hden] at h
      linarith [h]
    have hqp2 : (0:ℝ) < (96:ℝ)*qp^2 := by positivity
    have e : (Real.log 2)^2/(96*qp^2) * ((2*(m:ℝ)+2)*qp + qpp)
        = ((Real.log 2)^2 * ((2*(m:ℝ)+2)*qp + qpp)) / (96*qp^2) := by ring
    rw [le_div_iff₀ hden, e, div_le_iff₀ hqp2]
    linear_combination hL2
  have hd_ge : (1:ℝ) ≤ d * ((2*(m:ℝ)+2)*qp + qpp) := by
    have hden2 : (0:ℝ) < 2*(m:ℝ)+1+r+rho := by linarith [hmpos, hr, hrho]
    rw [hqpp_eq]
    have e : d * ((2*(m:ℝ)+2)*qp + r*qp) = (2*(m:ℝ)+2+r) / (2*(m:ℝ)+1+r+rho) := by
      rw [hdelta', div_mul_eq_mul_div, one_mul,
        div_eq_div_iff (ne_of_gt hpos) (ne_of_gt hden2)]
      ring
    rw [e, le_div_iff₀ hden2, one_mul]
    linarith [hrho1]
  have hstep2 : 2*qpp/((2*(m:ℝ)+2)*qp + qpp) ≤ 2*d*qpp := by
    have hnn : (0:ℝ) ≤ 2*qpp := by linarith [hqpp]
    have hmul := mul_nonneg (sub_nonneg.mpr hd_ge) hnn
    rw [div_le_iff₀ hden]
    linarith [hmul]
  have hstep3 : 2*d*qpp < 4*mu := by
    have h1 : (0:ℝ) < d*qp*(1-rho) := mul_pos (mul_pos hd hqp) (by linarith [hrho1])
    rw [hmudef, hqpp_eq, hdn_eq]
    linarith [h1]
  have hP6_4mu : P^2/6 < 4*mu := by linarith [hP6, hstep1, hstep2, hstep3]
  -- Step D: e^{P²/6} < A/(1−A) via 4μ ≤ ln(A/(1−A))
  have hA_ratio : A/(1-A) = (1+2*mu)/(1-2*mu) := by
    have h1 : ((1:ℝ)/2 - mu) ≠ 0 := ne_of_gt (by linarith [hmu_lt])
    have h2 : ((1:ℝ) - 2*mu) ≠ 0 := ne_of_gt (by linarith [hmu_lt])
    rw [h1mA_half, hA_half]
    field_simp
  have hlog4mu : 4*mu ≤ Real.log (A/(1-A)) := by
    rw [hA_ratio]
    have h := log_one_add_div_one_sub_ge (show (0:ℝ) ≤ 2*mu by linarith [hmu_pos])
      (show 2*mu < 1 by linarith [hmu_lt])
    linarith [h]
  have hexp : Real.exp (P^2/6) < A/(1-A) := by
    have hposA : (0:ℝ) < A/(1-A) := div_pos hA_pos h1mA_pos
    have h1 : Real.exp (P^2/6) < Real.exp (4*mu) := Real.exp_lt_exp.mpr hP6_4mu
    have h2 : Real.exp (4*mu) ≤ Real.exp (Real.log (A/(1-A))) :=
      Real.exp_le_exp.mpr hlog4mu
    rw [Real.exp_log hposA] at h2
    exact lt_of_lt_of_le h1 h2
  -- Step C: R ≤ e^{P²/6}
  have hup := gap_sinh_le_mul_exp P hP_nonneg
  have hQc_div : (1:ℝ) ≤ Real.sinh Qc / Qc := by
    rw [le_div_iff₀ hQc_pos, one_mul]
    exact sinh_ge_id hQc_nonneg
  have hR_C : R ≤ Real.exp (P^2/6) := by
    have hPQc : (0:ℝ) < P * Real.sinh Qc := mul_pos hP_pos hsinhQc
    have e : R = (Real.sinh P * Qc) / (P * Real.sinh Qc) := by
      rw [hRdef]; field_simp
    rw [e, div_le_iff₀ hPQc]
    have h1 : Real.sinh P * Qc ≤ (P * Real.exp (P^2/6)) * Qc :=
      mul_le_mul_of_nonneg_right hup hQc_nonneg
    have hsq := sinh_ge_id hQc_nonneg
    have h2 : (P * Real.exp (P^2/6)) * Qc ≤ (P * Real.exp (P^2/6)) * Real.sinh Qc :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg hP_pos.le (Real.exp_pos _).le)
    have h3 := le_trans h1 h2
    linear_combination h3
  have hR_lt : R < A/(1-A) := lt_of_le_of_lt hR_C hexp
  -- Step B: R < A/(1−A) gives (c₀/A)·sinh(P) < sinh(Qc)
  have hstepB : (c0/A) * Real.sinh P < Real.sinh Qc := by
    have key2 : (c0/A) * (Real.sinh P / Real.sinh Qc) < 1 := by
      have eR : Real.sinh P / Real.sinh Qc = R * (P / Qc) := by
        rw [hRdef]; field_simp
      have hPQc : P / Qc = (1-A)/c0 := by
        rw [hPdef, hQcdef, hc0def, hsdef]
        have hln2d : Real.log 2/(2*qp) ≠ 0 :=
          div_ne_zero (ne_of_gt hlog2) (mul_ne_zero (by norm_num) hqp_ne)
        field_simp
      have h4 : R * ((1-A)/A) < 1 := by
        have hpos1 : (0:ℝ) < (1-A)/A := div_pos h1mA_pos hA_pos
        have h5 : (A/(1-A)) * ((1-A)/A) = 1 := by field_simp
        calc R * ((1-A)/A) < (A/(1-A)) * ((1-A)/A) :=
              mul_lt_mul_of_pos_right hR_lt hpos1
          _ = 1 := h5
      have ealg : (c0/A) * (R * ((1-A)/c0)) = R * ((1-A)/A) := by
        field_simp
      have hrr : (c0/A) * (Real.sinh P / Real.sinh Qc) = (c0/A) * (R * ((1-A)/c0)) := by
        rw [eR, hPQc]
      rw [hrr, ealg]; exact h4
    have efin : (c0/A) * Real.sinh P
        = ((c0/A) * (Real.sinh P / Real.sinh Qc)) * Real.sinh Qc := by
      field_simp
    calc (c0/A) * Real.sinh P
        = ((c0/A) * (Real.sinh P / Real.sinh Qc)) * Real.sinh Qc := efin
      _ < 1 * Real.sinh Qc := mul_lt_mul_of_pos_right key2 hsinhQc
      _ = Real.sinh Qc := one_mul _
  -- assemble through the criterion
  have key : (qp / (((m:ℝ)+1)*qp+qpp))
      * Real.sinh (gapx (2*(m:ℝ)+1) d dn ((m:ℝ)+1) * Real.log 2 / 2)
      < Real.sinh (d * Real.log 2 / 2) := by
    rw [hQA, hx]
    have eParg : ((1-A)/qp) * Real.log 2 / 2 = P := by
      rw [hPdef, hsdef]; field_simp
    have eQcarg : d * Real.log 2 / 2 = Qc := by
      rw [hQcdef, hc0def, hsdef]; field_simp
    rw [eParg, eQcarg]
    exact hstepB
  have hfin : gapDeltaLogT qp qpp d dn (2*(m:ℝ)+1) (m:ℝ)
      = Real.log (1 - (qp / (((m:ℝ)+1)*qp+qpp))^2) +
        Real.log (((2:ℝ)^(gapx (2*(m:ℝ)+1) d dn ((m:ℝ)+1)) - 1)^2 /
          (((2:ℝ)^(gapx (2*(m:ℝ)+1) d dn ((m:ℝ)+1) + d) - 1)
            * ((2:ℝ)^(gapx (2*(m:ℝ)+1) d dn ((m:ℝ)+1) - d) - 1))) := by
    unfold gapDeltaLogT
    rw [show gapQ qp qpp ((m:ℝ)+1) = (((m:ℝ)+1)*qp+qpp) from rfl]
  rw [hfin]
  exact hgt.mpr key

end GapCF
