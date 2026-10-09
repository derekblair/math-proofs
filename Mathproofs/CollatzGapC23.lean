import Mathproofs.CollatzGapConvex
import Mathproofs.CollatzGapC24
import Mathproofs.CollatzGapSinh
import Mathlib.Analysis.Convex.Deriv

open scoped Nat

/-!
# C23 assembly: hyperbolic lemmas for the even-a selector (R77)

Source: `~/workspace/math-unsolved/c23_proofs_r27.md` (Round 27).

C23 resolves the even-a split: on a from-above block with even `a_n = 2m ≥ 4`,
the argmin `t*` of `G` is `m` or `m-1`, decided by the selector `ρ ⋚ r`
(C24 Lemma 2, now [PROVED], gives `ρ ⋚ r ↔ T ⋛ M`; C24 Lemma 3, now [PROVED],
decides `T ⋛ M` by the finite first-difference rule).

This module machine-checks the two hyperbolic estimates at the heart of
C23's proof (Steps 2–3 of `c23_proofs_r27.md`):

- `sinh_scaling_gt` (Step 2, part (a)): for `t₀ > 1`, `s₀ > 0`,
  `sinh(t₀·s₀) > t₀·sinh(s₀)`. Via strict convexity of `sinh` on `[0,∞)`
  (`strictConvexOn_sinh_Ici`, from `strictConvexOn_of_deriv2_pos` since
  `sinh'' = sinh > 0` on `(0,∞)`), with weights `1/t₀`, `1 − 1/t₀`.
- `sinh_upper_exp` (Step 3, part (b)): for `w ≥ 0`,
  `sinh w ≤ w·exp(w²/6)`. Termwise from the Taylor series
  `sinh w = ∑ w^{2k+1}/(2k+1)!`, using `(2k+1)! ≥ 6^k·k!`.

The full C23(a) assembly (wiring these through the R24 criterion
`gap_criterion_CF`, C18b `gapDelta_strictly_increasing`, and C21's range
to the argmin conclusion `t* = m` / `t* = m-1`) is in progress: R81 added
the Step-0 argmin logic (`gap_argmin_step0`), the selector bridge
(`c23a_selector_ge`, from C24 Lemma 2), the Δ-sign core
(`c23a_delta_neg`, via `gap_criterion_CF` + `sinh_scaling_gt`), and the
assembled `c23a` (variable identifications as explicit hypotheses).
`gap_sinh_le_mul_exp` (sub-lemma E, the C23(b) series bound, proved R37)
had its axioms recorded in R81. C23(b)'s `K(n)`-threshold chain
(`ln(1+x) ≥ x/(1+x)` is `gap_log_one_add_ge`, axioms recorded R81) was
formalized in R85: `det_block_form` (the determinant in block form from
`cf_det_identity`), `delta'_formula`, the `(‡)` algebra
(`dagger_sufficient`), `c23b_delta_pos`, assembled `c23b`, plus the
`gapDelta = gapDeltaLog` bridge (`gapDelta_gapDeltaLog`).

Checked with Lean 4.34.1 + Mathlib v4.34.1 on xavier, zero sorrys.
-/

namespace GapCF

/-- `sinh` is strictly convex on `[0, ∞)`: `sinh'' = sinh > 0` on the
interior `(0, ∞)`. -/
theorem strictConvexOn_sinh_Ici :
    StrictConvexOn ℝ (Set.Ici 0) Real.sinh := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0) Real.continuous_sinh.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  have hx0 : (0:ℝ) < x := hx
  have h2 : (deriv^[2] Real.sinh) x = Real.sinh x := by
    show deriv (deriv Real.sinh) x = Real.sinh x
    rw [Real.deriv_sinh, Real.deriv_cosh]
  rw [h2]
  exact Real.sinh_pos_iff.mpr hx0

/-- C23(a) key estimate: scaling the argument of `sinh` by `t₀ > 1`
outgrows scaling the value. For `t₀ > 1`, `s₀ > 0`:
`sinh(t₀·s₀) > t₀·sinh(s₀)`. -/
theorem sinh_scaling_gt {t₀ s₀ : ℝ} (ht : 1 < t₀) (hs : 0 < s₀) :
    t₀ * Real.sinh s₀ < Real.sinh (t₀ * s₀) := by
  have hconv := strictConvexOn_sinh_Ici
  have ht0 : (0:ℝ) < t₀ := lt_trans zero_lt_one ht
  have hxmem : t₀ * s₀ ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr (mul_nonneg (le_of_lt ht0) (le_of_lt hs))
  have hymem : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr le_rfl
  have hne : t₀ * s₀ ≠ 0 := ne_of_gt (mul_pos ht0 hs)
  have ha : (0:ℝ) < 1 / t₀ := by positivity
  have hb : (0:ℝ) < 1 - 1 / t₀ := by
    rw [sub_pos, div_lt_one ht0]
    exact ht
  have hab : 1 / t₀ + (1 - 1 / t₀) = 1 := by ring
  obtain ⟨_, hsc⟩ := hconv
  have h := hsc hxmem hymem hne (a := 1 / t₀) (b := 1 - 1 / t₀) ha hb hab
  -- `h : sinh ((1/t₀) • (t₀*s₀) + (1-1/t₀) • 0) < (1/t₀) • sinh(t₀*s₀) + (1-1/t₀) • sinh 0`
  simp only [smul_eq_mul] at h
  have harg : (1 / t₀) * (t₀ * s₀) = s₀ := by
    field_simp
  rw [harg, Real.sinh_zero, mul_zero] at h
  have h2 : Real.sinh s₀ < 1 / t₀ * Real.sinh (t₀ * s₀) := by
    simpa using h
  -- `h2 : sinh s₀ < (1/t₀) * sinh (t₀*s₀)`
  have ht0ne : t₀ ≠ 0 := ne_of_gt ht0
  calc t₀ * Real.sinh s₀ < t₀ * ((1 / t₀) * Real.sinh (t₀ * s₀)) :=
        mul_lt_mul_of_pos_left h2 ht0
    _ = Real.sinh (t₀ * s₀) := by
        rw [← mul_assoc, mul_one_div_cancel ht0ne, one_mul]

/-! ## C23(a) assembly: `ρ ≥ r ⟹ Δ(m-1) < 0 ⟹ t* = m` (R81)

Source: `~/workspace/math-unsolved/c23_proofs_r27.md` Steps 0–2.

The assembly wires three proved inputs:
- `c23a_selector_ge` — C24 Lemma 2 (`cf_selector_lt`), non-strict:
  `T ≤ M ⟹ r ≤ ρ` (the `ρ ≥ r` case hypothesis, from the CF side);
- `c23a_delta_neg` — the Δ-sign core: `ρ ≥ r ⟹ Δ(m-1) < 0`
  (in the criterion's exact log form `gapDeltaLog`), via `gap_criterion_CF`
  at `t = m-1` and `sinh_scaling_gt`;
- `gap_argmin_step0` — the Step-0 argmin logic: `Δ(m-1) < 0 ⟹ t* = m`
  given `t* ∈ {m-1, m}` (the C21 range as hypothesis).

The assembled `c23a` takes the CF/analysis variable identifications
(`δ_n = ρ·δ′`, `q″ = r·q′`) and the `Δ = g(m) − g(m-1)` bridge as explicit
hypotheses; closing those bridges against the `GapCF` CF API
(`cerr`, `Q`, `cquot`) and the `gapDelta` definition is the remaining
wiring (recorded in `ROUND81_DOSSIER.md`). -/

/-- Step-0 argmin logic (C23 Step 0): if `tstar` minimizes `g` on the C21
range `{m-1, m}` and `g m < g (m-1)` (i.e. `Δ(m-1) < 0`), then `tstar = m`. -/
theorem gap_argmin_step0 (g : ℕ → ℝ) (m tstar : ℕ)
    (hmem : tstar = m - 1 ∨ tstar = m)
    (harg : ∀ t : ℕ, t = m - 1 ∨ t = m → g tstar ≤ g t)
    (hlt : g m < g (m - 1)) :
    tstar = m := by
  rcases hmem with h | h
  · exfalso
    have hle := harg m (Or.inr rfl)
    rw [h] at hle
    linarith
  · exact h

/-- Selector bridge (C24 Lemma 2, non-strict): `T ≤ M ⟹ r ≤ ρ`.
From `cf_selector_lt` (`ρ < r ↔ M < T`) by contraposition. -/
theorem c23a_selector_ge {α : ℝ} (hirr : Irrational α) (n : ℕ)
    (h : cquot α (n + 3) ≤ Q α (n + 1) / Q α n) :
    Q α n / Q α (n + 1) ≤ |cerr α (n + 2)| / |cerr α (n + 1)| := by
  have hiff := (cf_selector_lt hirr n).not
  have h2 : ¬ (Q α (n + 1) / Q α n < cquot α (n + 3)) := not_lt.mpr h
  exact not_lt.mp (hiff.mpr h2)

/-- C23(a) Δ-sign core (Steps 1–2): on a from-above block with `a = 2m`,
`m ≥ 2`, if `ρ ≥ r` (with `δ_n = ρ·δ′`, `q″ = r·q′`), then `Δ(m-1) < 0`,
in the criterion's exact log form `gapDeltaLog`.
Via `gap_criterion_CF` at `t = m-1`: it suffices that
`sinh((m+ρ)·s₀) > (m+r)·sinh(s₀)` for `s₀ = δ′·ln2/2 > 0`, which follows
from `sinh_scaling_gt` and `(m+r)·sinh(s₀) ≤ (m+ρ)·sinh(s₀)`. -/
theorem c23a_delta_neg {qp qpp d dn rho r m : ℝ}
    (hm : 2 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d)
    (hrho : 0 < rho) (hr : 0 < r) (hrr : r ≤ rho)
    (hdn : dn = rho * d) (hqpp_eq : qpp = r * qp) :
    gapDeltaLog qp qpp d dn m < 0 := by
  have hdn_pos : 0 < dn := by rw [hdn]; positivity
  have ht1 : (1:ℝ) ≤ m - 1 := by linarith
  have ht2 : (m - 1) + 1 ≤ 2 * m - 1 := by linarith
  have hcrit := gap_criterion_CF (a := 2 * m) (t := m - 1) hqp hqpp hd hdn_pos ht1 ht2
  rw [show (m:ℝ) - 1 + 1 = m by ring] at hcrit
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hs0 : (0:ℝ) < d * Real.log 2 / 2 := div_pos (mul_pos hd hlog2) (by norm_num)
  have hxm : gapx (2*m) d dn m = (m + rho) * d := by
    unfold gapx; rw [hdn]; ring
  have hQm : gapQ qp qpp m = (m + r) * qp := by
    unfold gapQ; rw [hqpp_eq]; ring
  have hscale := sinh_scaling_gt (show (1:ℝ) < m + rho by linarith) hs0
  have hmono : (m + r) * Real.sinh (d * Real.log 2 / 2)
      ≤ (m + rho) * Real.sinh (d * Real.log 2 / 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (Real.sinh_pos_iff.mpr hs0))
  have hlt : (m + r) * Real.sinh (d * Real.log 2 / 2)
      < Real.sinh ((m + rho) * (d * Real.log 2 / 2)) :=
    lt_of_le_of_lt hmono hscale
  have hmr : (0:ℝ) < m + r := by linarith
  have hmrne : m + r ≠ 0 := ne_of_gt hmr
  have hQmne : gapQ qp qpp m ≠ 0 := by rw [hQm]; exact ne_of_gt (mul_pos hmr hqp)
  have hfrac : qp / gapQ qp qpp m = 1 / (m + r) := by
    rw [div_eq_div_iff hQmne hmrne, hQm]
    ring
  have harg : ((m + rho) * d) * Real.log 2 / 2
      = (m + rho) * (d * Real.log 2 / 2) := by ring
  have key : Real.sinh (d * Real.log 2 / 2)
      < (qp / gapQ qp qpp m) * Real.sinh (gapx (2*m) d dn m * Real.log 2 / 2) := by
    rw [hfrac, hxm, harg, div_mul_eq_mul_div, one_mul, lt_div_iff₀ hmr, mul_comm]
    exact hlt
  exact hcrit.mpr key

/-- **C23(a)** (`c23_proofs_r27.md`): on a from-above block with even
`a = 2m ≥ 4`, if `ρ ≥ r` and `tstar` is the argmin of `g = ln G` on the
C21 range `{m-1, m}`, then `tstar = m`.
The variable identifications (`δ_n = ρ·δ′`, `q″ = r·q′`) and the
`Δ(m-1) = g(m) − g(m-1)` bridge (criterion's log form) are explicit
hypotheses; `c23a_selector_ge` supplies `r ≤ ρ` from the CF tail
comparison `T ≤ M`. -/
theorem c23a {g : ℕ → ℝ} {tstar m : ℕ} {qp qpp d dn rho r : ℝ}
    (hm : 2 ≤ m)
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d)
    (hrho : 0 < rho) (hr : 0 < r) (hrr : r ≤ rho)
    (hdn : dn = rho * d) (hqpp_eq : qpp = r * qp)
    (hmem : tstar = m - 1 ∨ tstar = m)
    (harg : ∀ t : ℕ, t = m - 1 ∨ t = m → g tstar ≤ g t)
    (hdelta : g m - g (m - 1) = gapDeltaLog qp qpp d dn (m : ℝ)) :
    tstar = m := by
  have hmR : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hneg := c23a_delta_neg hmR hqp hqpp hd hrho hr hrr hdn hqpp_eq
  have hlt : g m < g (m - 1) := by linarith
  exact gap_argmin_step0 g m tstar hmem harg hlt

/-! ## C23(b) prerequisites (R81)

C23(b) (`c23_proofs_r27.md` Step 3) needs, beyond the R81-proved
`gap_sinh_le_mul_exp` (upper series bound) and `gap_log_one_add_ge`
(`ln(1+x) ≥ x/(1+x)`, axioms recorded R81):
- `sinh_ge_id` — the lower bound `x ≤ sinh x` (`x ≥ 0`), proved here;
- the `δ'`-formula `δ' = 1/(q'(a+r+ρ))` from `cf_det_identity`
  (CF block-index wiring — next lane);
- the `(‡)` sufficient-condition algebra from the `K(n)` threshold
  (pure real analysis given the above — next lane). -/

/-- Lower series bound for C23(b): `x ≤ sinh x` for `x ≥ 0`.
The Taylor series `sinh x = ∑ x^{2n+1}/(2n+1)!` has first term `x`
and all terms nonneg. -/
theorem sinh_ge_id {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.sinh x := by
  rw [Real.sinh_eq_tsum]
  have hnn : ∀ n : ℕ, 0 ≤ x ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) :=
    fun n => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)
  have hle := (Real.hasSum_sinh x).summable.le_tsum 0 (fun j _ => hnn j)
  simpa using hle

/-! ## C23(b) `K(n)`-threshold chain (R85)

Source: `~/workspace/math-unsolved/c23_proofs_r27.md` Step 3.

C23(b): on a from-above block with even `a = 2m ≥ 4`, if `ρ < r` and the
`K(n)` threshold `q′²(r−ρ) ≥ 3(ln2)²/128·(m+1)` holds, then `Δ(m−1) > 0`,
so `t* = m−1`.

Ingredients (all [PROVED]):
- `det_block_form` — the determinant `q_n·δ' + q'·δ_n = 1` in block form,
  from `cf_det_identity` at even `m = n−1` (n odd);
- `delta'_formula` — `δ' = 1/(q'(a+r+ρ))` from the determinant,
  `δ_n = ρ·δ'`, and `q_n = (a+r)·q'`;
- `dagger_sufficient` — the `(‡)` sufficient-condition algebra: the `K(n)`
  threshold implies `((m+ρ)s₀)²/6 ≤ ln(1+(r−ρ)/(m+ρ))`, via the clean bounds
  LHS `≤ 3z²/(32q'²)` (using `ρ<1`, `a+r+ρ>a`, `(m+1)/(2m)≤3/4` for `m≥2`)
  and RHS `≥ (r−ρ)/(m+1)` (using `ln(1+x) ≥ x/(1+x)`, `r<1`);
- `c23b_delta_pos` — the Δ-sign core: `ρ < r` + `K(n)` ⟹
  `0 < gapDeltaLog` (criterion's exact log form), via `gap_delta_sign_gt`,
  `gap_sinh_le_mul_exp` (upper), strict `sinh_ge_id_pos` (lower), and `(‡)`;
- `c23b` — assembled C23(b): `tstar = m−1`.

Also: `gapDelta_gapDeltaLog` — the exact bridge identifying
`gapDelta qp qpp (2m) d e (m−1)` (T-diff + S-diff) with the criterion's
log-sum `gapDeltaLog qp qpp d e m` (uses `Q_{t+1} = Q_t + q′` for the T-part
and `u(t) = u(t+1) + d` for the S-part); closes the `hdelta` hypothesis of
`c23a`/`c23b` up to the `g = ln G` identification. -/

/-- Determinant identity in block form: from `cf_det_identity` at even
`m = n−1` (n odd). The index identifications `qn = Q α n`,
`qp = Q α (n−1)`, `d = δ' = |cerr α (n−1)|`, `dn = δ_n = |cerr α n|`
are explicit hypotheses. This is the `(F1)` input
`q_n·δ' + q'·δ_n = 1` for the C22/C23/C25 assembly. -/
theorem det_block_form {α : ℝ} (hirr : Irrational α) (n : ℕ)
    (hn : Odd n) (hn1 : 1 ≤ n)
    {qn qp d dn : ℝ}
    (hqn : qn = Q α n) (hqp : qp = Q α (n - 1))
    (hd : d = |cerr α (n - 1)|) (hdn : dn = |cerr α n|) :
    qn * d + qp * dn = 1 := by
  have hev : Even (n - 1) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, by omega⟩
  have hdet := cf_det_identity hirr (n - 1) hev
  have h1 : (n - 1) + 1 = n := by omega
  rw [h1] at hdet
  rw [hqn, hqp, hd, hdn]
  exact hdet

/-- The `δ'`-formula: from `q_n·δ' + q'·δ_n = 1` (block-form determinant),
`δ_n = ρ·δ'`, `q_n = (a+r)·q'`: `δ' = 1/(q'(a+r+ρ))`. -/
theorem delta'_formula {qn qp d dn rho r a : ℝ}
    (hdet : qn * d + qp * dn = 1)
    (hdn : dn = rho * d) (hqn : qn = (a + r) * qp)
    (hqp : 0 < qp) (hsum : 0 < a + r + rho) :
    d = 1 / (qp * (a + r + rho)) := by
  have h2 : ((a + r + rho) * qp) * d = 1 := by
    have h3 : ((a + r + rho) * qp) * d = qn * d + qp * dn := by
      rw [hdn, hqn]; ring
    rw [h3]; exact hdet
  calc d = ((a + r + rho) * qp)⁻¹ := eq_inv_of_mul_eq_one_right h2
    _ = 1 / (qp * (a + r + rho)) := by rw [inv_eq_one_div, mul_comm]

/-- Strict lower series bound for C23(b): `x < sinh x` for `x > 0`.
The Taylor series has `0`-term `x`, `1`-term `x³/6 > 0`, all terms nonneg. -/
theorem sinh_ge_id_pos {x : ℝ} (hx : 0 < x) : x < Real.sinh x := by
  rw [Real.sinh_eq_tsum]
  have hs := (Real.hasSum_sinh x).summable
  have hnn : ∀ n : ℕ, 0 ≤ x ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) :=
    fun n => div_nonneg (pow_nonneg (le_of_lt hx) _) (Nat.cast_nonneg _)
  have h01 := Summable.sum_le_tsum ({0, 1} : Finset ℕ) (fun i _ => hnn i) hs
  have hsum : ({0, 1} : Finset ℕ).sum (fun n => x ^ (2 * n + 1) / ((2 * n + 1)! : ℝ))
      = x + x ^ 3 / 6 := by
    have e0 : x ^ (2 * 0 + 1) / (((2 * 0 + 1)!) : ℝ) = x := by
      have h1 : (2 * 0 + 1 : ℕ) = 1 := rfl
      have h2 : ((1 : ℕ)! : ℕ) = 1 := rfl
      rw [h1, h2]
      norm_num
    have e1 : x ^ (2 * 1 + 1) / (((2 * 1 + 1)!) : ℝ) = x ^ 3 / 6 := by
      have h1 : (2 * 1 + 1 : ℕ) = 3 := rfl
      have h2 : ((3 : ℕ)! : ℕ) = 6 := rfl
      rw [h1, h2]
      norm_num
    calc ({0, 1} : Finset ℕ).sum (fun n => x ^ (2 * n + 1) / ((2 * n + 1)! : ℝ))
        = x ^ (2 * 0 + 1) / (((2 * 0 + 1)!) : ℝ)
          + (x ^ (2 * 1 + 1) / (((2 * 1 + 1)!) : ℝ)) := by
          rw [Finset.sum_pair (by norm_num)]
      _ = x + x ^ 3 / 6 := by rw [e0, e1]
  rw [hsum] at h01
  have hx3 : (0:ℝ) < x ^ 3 / 6 := by positivity
  linarith

/-- Clean LHS bound for `(‡)`: `((m+ρ)s₀)²/6 ≤ 3z²/(32q'²)` with
`z = ln2/2`, `s₀ = z/(q'(a+r+ρ))`, `a = 2m`.
Uses `ρ<1`, `a+r+ρ>a` (so `(m+ρ)/(a+r+ρ) ≤ (m+1)/a`), and
`(m+1)/(2m) ≤ 3/4` for `m ≥ 2`. -/
theorem dagger_lhs_bound {qp rho r m s0 : ℝ}
    (hm : 2 ≤ m) (hqp : 0 < qp)
    (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hr0 : 0 < r)
    (hs0 : s0 = (Real.log 2 / 2) / (qp * (2 * m + r + rho))) :
    ((m + rho) * s0)^2 / 6 ≤ 3 * (Real.log 2 / 2)^2 / (32 * qp^2) := by
  have hS : (0:ℝ) < 2 * m + r + rho := by
    have h2m : (0:ℝ) < 2 * m := by linarith
    linarith [hr0, hrho0]
  have hSne : (2 * m + r + rho) ≠ 0 := ne_of_gt hS
  have h2m : (0:ℝ) < 2 * m := by linarith
  have hfrac : (m + rho) / (2*m + r + rho) ≤ (m+1) / (2*m) := by
    rw [div_le_iff₀ hS, div_mul_eq_mul_div, le_div_iff₀ h2m]
    have key : (0:ℝ) ≤ m * r + m * (2 - rho) + r + rho := by
      have g1 := mul_nonneg (show (0:ℝ) ≤ m by linarith) (show (0:ℝ) ≤ r by linarith)
      have g2 := mul_nonneg (show (0:ℝ) ≤ m by linarith) (show (0:ℝ) ≤ 2 - rho by linarith)
      linarith
    nlinarith [key]
  have hfracnn : (0:ℝ) ≤ (m + rho) / (2*m + r + rho) := by positivity
  have hsq : ((m+rho)/(2*m+r+rho))^2 ≤ ((m+1)/(2*m))^2 := by
    have hnn := mul_nonneg (sub_nonneg.mpr hfrac) (add_nonneg hfracnn (le_trans hfracnn hfrac))
    nlinarith [hnn]
  have h34 : ((m+1)/(2*m))^2 ≤ 9/16 := by
    have h1 : (m+1)/(2*m) ≤ 3/4 := by
      rw [div_le_iff₀ h2m]
      linarith
    have h0 : (0:ℝ) ≤ (m+1)/(2*m) := by positivity
    have hnn := mul_nonneg (sub_nonneg.mpr h1) (add_nonneg (show (0:ℝ) ≤ 3/4 by norm_num) h0)
    nlinarith [hnn]
  have hC : (0:ℝ) ≤ (Real.log 2/2)^2/(6*qp^2) := by positivity
  have hrewrite : ((m+rho)*s0)^2/6
      = ((m+rho)/(2*m+r+rho))^2 * ((Real.log 2/2)^2/(6*qp^2)) := by
    rw [hs0]
    have hqpne : qp ≠ 0 := ne_of_gt hqp
    field_simp
  rw [hrewrite]
  have hAsq : ((m+rho)/(2*m+r+rho))^2 ≤ 9/16 := le_trans hsq h34
  calc ((m+rho)/(2*m+r+rho))^2 * ((Real.log 2/2)^2/(6*qp^2))
      ≤ (9/16) * ((Real.log 2/2)^2/(6*qp^2)) :=
        mul_le_mul_of_nonneg_right hAsq hC
    _ = 3 * (Real.log 2/2)^2/(32*qp^2) := by ring

/-- Clean RHS bound for `(‡)`: `(r−ρ)/(m+1) ≤ ln(1+(r−ρ)/(m+ρ))`.
From `ln(1+x) ≥ x/(1+x)` (`gap_log_one_add_ge`) with `x = (r−ρ)/(m+ρ)`,
and `(r−ρ)/(m+r) ≥ (r−ρ)/(m+1)` using `r < 1`. -/
theorem dagger_rhs_bound {rho r m : ℝ}
    (hm : 2 ≤ m) (hrho0 : 0 < rho) (hr1 : r < 1) (hrr : rho < r) :
    (r - rho) / (m + 1) ≤ Real.log (1 + (r - rho) / (m + rho)) := by
  have hmp : (0:ℝ) < m + rho := by linarith
  have hx : (0:ℝ) < (r - rho) / (m + rho) := by positivity
  have hlog := gap_log_one_add_ge ((r - rho) / (m + rho)) hx
  have heq : ((r - rho) / (m + rho)) / (1 + (r - rho) / (m + rho))
      = (r - rho) / (m + r) := by
    have hne : (m + rho) ≠ 0 := ne_of_gt hmp
    have hmr : (m + r) ≠ 0 := ne_of_gt (by linarith)
    have e1 : (1:ℝ) + (r - rho) / (m + rho) = (m + r) / (m + rho) := by
      rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne, one_mul]
      ring
    have hY : ((m + r) / (m + rho)) ≠ 0 := div_ne_zero hmr hne
    rw [e1, div_eq_iff hY, div_mul_div_comm, div_eq_div_iff hne (mul_ne_zero hmr hne)]
    ring
  rw [heq] at hlog
  have hle : (r - rho) / (m + 1) ≤ (r - rho) / (m + r) := by
    rw [div_le_div_iff_of_pos_left (by linarith) (by linarith) (by linarith)]
    linarith
  linarith

/-- Middle bridge for `(‡)`: the `K(n)` threshold gives
`3z²/(32q'²) ≤ (r−ρ)/(m+1)` (with `z = ln2/2`, so `3z²/32 = 3(ln2)²/128`). -/
theorem dagger_bridge {qp rho r m : ℝ}
    (hqp : 0 < qp) (hrho0 : 0 < rho) (hrr : rho < r) (hm : 2 ≤ m)
    (hK : 3 * (Real.log 2)^2 / 128 * (m + 1) ≤ qp^2 * (r - rho)) :
    3 * (Real.log 2 / 2)^2 / (32 * qp^2) ≤ (r - rho) / (m + 1) := by
  have h1 : (0:ℝ) < 32 * qp^2 := by positivity
  have h2 : (0:ℝ) < m + 1 := by linarith
  rw [div_le_iff₀ h1, div_mul_eq_mul_div, le_div_iff₀ h2]
  have hK2 := mul_le_mul_of_nonneg_right hK (show (0:ℝ) ≤ 32 by norm_num)
  nlinarith [hK2]

/-- C23(b) `(‡)` sufficient-condition algebra: the `K(n)` threshold
`q′²(r−ρ) ≥ 3(ln2)²/128·(m+1)` implies the checkable inequality
`((m+ρ)s₀)²/6 ≤ ln(1+(r−ρ)/(m+ρ))`. -/
theorem dagger_sufficient {qp rho r m s0 : ℝ}
    (hm : 2 ≤ m) (hqp : 0 < qp)
    (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hrr : rho < r)
    (hs0 : s0 = (Real.log 2 / 2) / (qp * (2 * m + r + rho)))
    (hK : 3 * (Real.log 2)^2 / 128 * (m + 1) ≤ qp^2 * (r - rho)) :
    ((m + rho) * s0)^2 / 6 ≤ Real.log (1 + (r - rho) / (m + rho)) :=
  le_trans (dagger_lhs_bound hm hqp hrho0 hrho1 hr0 hs0)
    (le_trans (dagger_bridge hqp hrho0 hrr hm hK) (dagger_rhs_bound hm hrho0 hr1 hrr))

/-- C23(b) Δ-sign core (Step 3): on a from-above block with `a = 2m`,
`m ≥ 2`, if `ρ < r` (with `δ_n = ρ·δ′`, `q″ = r·q′`), the `δ'`-formula
`δ' = 1/(q'(a+r+ρ))`, and the `K(n)` threshold holds, then `Δ(m-1) > 0`,
in the criterion's exact log form `gapDeltaLog`.
Via `gap_delta_sign_gt` at `t = m-1`: it suffices that
`sinh((m+ρ)·s₀) < (m+r)·sinh(s₀)` for `s₀ = δ′·ln2/2 > 0`, which follows
from `gap_sinh_le_mul_exp` (upper), the `(‡)` cleanup
(`(m+ρ)·exp(X) ≤ m+r`), and strict `sinh_ge_id_pos` (lower). -/
theorem c23b_delta_pos {qp qpp d dn rho r m : ℝ}
    (hm : 2 ≤ m) (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d)
    (hrho : 0 < rho) (hrho1 : rho < 1) (hr : 0 < r) (hr1 : r < 1) (hrr : rho < r)
    (hdn : dn = rho * d) (hqpp_eq : qpp = r * qp)
    (hdelta' : d = 1 / (qp * (2 * m + r + rho)))
    (hK : 3 * (Real.log 2)^2 / 128 * (m + 1) ≤ qp^2 * (r - rho)) :
    0 < gapDeltaLog qp qpp d dn m := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmr : (0:ℝ) < m + r := by linarith
  have hmrho : (0:ℝ) < m + rho := by linarith
  have hxm : gapx (2*m) d dn m = (m + rho) * d := by
    unfold gapx; rw [hdn]; ring
  have hQm : gapQ qp qpp m = (m + r) * qp := by
    unfold gapQ; rw [hqpp_eq]; ring
  have hQmpos : qp < gapQ qp qpp m := by
    rw [hQm]
    have h1 : (0:ℝ) < (m + r - 1) * qp := mul_pos (by linarith) hqp
    linarith
  have hvm : d < gapx (2*m) d dn m := by
    rw [hxm]
    have h1 : (0:ℝ) < (m + rho - 1) * d := mul_pos (by linarith) hd
    linarith
  have hgt := gap_delta_sign_gt (gapQ qp qpp m) qp (gapx (2*m) d dn m) d
    hqp hQmpos hd hvm
  have hlog : gapDeltaLog qp qpp d dn m
      = Real.log (1 - (qp / gapQ qp qpp m)^2) +
        Real.log (((2:ℝ)^(gapx (2*m) d dn m) - 1)^2 /
          (((2:ℝ)^(gapx (2*m) d dn m + d) - 1) * ((2:ℝ)^(gapx (2*m) d dn m - d) - 1))) := rfl
  rw [hlog]
  apply hgt.mpr
  rw [hQm, hxm]
  have hfrac : qp / ((m + r) * qp) = 1 / (m + r) := by
    rw [div_eq_div_iff (mul_ne_zero (ne_of_gt hmr) (ne_of_gt hqp)) (ne_of_gt hmr)]
    ring
  rw [hfrac]
  have harg : (m + rho) * d * Real.log 2 / 2 = (m + rho) * (d * Real.log 2 / 2) := by ring
  rw [harg]
  set s0 : ℝ := d * Real.log 2 / 2 with hs0def
  have hs0 : (0:ℝ) < s0 := by rw [hs0def]; exact div_pos (mul_pos hd hlog2) (by norm_num)
  have hs0eq : s0 = (Real.log 2 / 2) / (qp * (2 * m + r + rho)) := by
    rw [hs0def, hdelta']
    have hne1 : qp ≠ 0 := ne_of_gt hqp
    have hne2 : (2*m + r + rho) ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have hdag := dagger_sufficient hm hqp hrho hrho1 hr hr1 hrr hs0eq hK
  have hpos1 : (0:ℝ) < 1 + (r - rho) / (m + rho) := by positivity
  have hexp : Real.exp (((m + rho) * s0)^2 / 6) ≤ (m + r) / (m + rho) := by
    have e1 : Real.exp (((m + rho) * s0)^2 / 6)
        ≤ Real.exp (Real.log (1 + (r - rho) / (m + rho))) :=
      Real.exp_le_exp.mpr hdag
    rw [Real.exp_log hpos1] at e1
    have e2 : (1:ℝ) + (r - rho) / (m + rho) = (m + r) / (m + rho) := by
      have hne : (m + rho) ≠ 0 := ne_of_gt hmrho
      field_simp
      ring
    rwa [e2] at e1
  have hmul : (m + rho) * Real.exp (((m + rho) * s0)^2 / 6) ≤ m + r := by
    have hle := mul_le_mul_of_nonneg_left hexp (le_of_lt hmrho)
    have heq : (m + rho) * ((m + r) / (m + rho)) = m + r := by
      have hne : (m + rho) ≠ 0 := ne_of_gt hmrho
      field_simp
    rwa [heq] at hle
  have hup := gap_sinh_le_mul_exp ((m + rho) * s0)
    (mul_nonneg (le_of_lt hmrho) (le_of_lt hs0))
  have hlow : s0 < Real.sinh s0 := sinh_ge_id_pos hs0
  have h1mr : (0:ℝ) ≤ 1 / (m + r) := by positivity
  calc (1/(m+r)) * Real.sinh ((m+rho)*s0)
      ≤ (1/(m+r)) * ((m+rho)*s0 * Real.exp (((m+rho)*s0)^2/6)) :=
        mul_le_mul_of_nonneg_left hup h1mr
    _ = s0 * ((m+rho) * Real.exp (((m+rho)*s0)^2/6) / (m+r)) := by ring
    _ ≤ s0 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hs0)
        rw [div_le_one hmr]
        exact hmul
    _ = s0 := mul_one s0
    _ < Real.sinh s0 := hlow

/-- Step-0 argmin logic, `>` mirror (C23 Step 0): if `tstar` minimizes `g`
on the C21 range `{m-1, m}` and `g (m-1) < g m` (i.e. `Δ(m-1) > 0`),
then `tstar = m - 1`. -/
theorem gap_argmin_step0_gt (g : ℕ → ℝ) (m tstar : ℕ)
    (hmem : tstar = m - 1 ∨ tstar = m)
    (harg : ∀ t : ℕ, t = m - 1 ∨ t = m → g tstar ≤ g t)
    (hlt : g (m - 1) < g m) :
    tstar = m - 1 := by
  rcases hmem with h | h
  · exact h
  · exfalso
    have hle := harg (m - 1) (Or.inl rfl)
    rw [h] at hle
    linarith

/-- **C23(b)** (`c23_proofs_r27.md` Step 3): on a from-above block with even
`a = 2m ≥ 4`, if `ρ < r`, the `K(n)` threshold
`q′²(r−ρ) ≥ 3(ln2)²/128·(m+1)` holds, and `tstar` is the argmin of
`g = ln G` on the C21 range `{m-1, m}`, then `tstar = m - 1`.
The `δ'`-formula (`delta'_formula` from `det_block_form`), the variable
identifications (`δ_n = ρ·δ′`, `q″ = r·q′`), and the `Δ(m-1)` bridge
(criterion's log form) are explicit hypotheses; `gapDelta_gapDeltaLog`
closes the bridge up to the `g = ln G` identification. -/
theorem c23b {g : ℕ → ℝ} {tstar m : ℕ} {qp qpp d dn rho r : ℝ}
    (hm : 2 ≤ m)
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d)
    (hrho : 0 < rho) (hrho1 : rho < 1) (hr : 0 < r) (hr1 : r < 1) (hrr : rho < r)
    (hdn : dn = rho * d) (hqpp_eq : qpp = r * qp)
    (hdelta' : d = 1 / (qp * (2*(m:ℝ) + r + rho)))
    (hK : 3 * (Real.log 2)^2 / 128 * ((m:ℝ) + 1) ≤ qp^2 * (r - rho))
    (hmem : tstar = m - 1 ∨ tstar = m)
    (harg : ∀ t : ℕ, t = m - 1 ∨ t = m → g tstar ≤ g t)
    (hdelta : g m - g (m - 1) = gapDeltaLog qp qpp d dn (m : ℝ)) :
    tstar = m - 1 := by
  have hmR : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hpos := c23b_delta_pos hmR hqp hqpp hd hrho hrho1 hr hr1 hrr hdn hqpp_eq hdelta' hK
  have hlt : g (m - 1) < g m := by linarith
  exact gap_argmin_step0_gt g m tstar hmem harg hlt

/-! ## `gapDelta = gapDeltaLog` bridge (R85)

The exact algebra identifying `gapDelta qp qpp a d e t` (T-diff + S-diff)
with the criterion's log-sum. Uses `Q_{t+1} = Q_t + q′` for the T-part
and `u(t) = u(t+1) + d` for the S-part. Closes the `hdelta` hypothesis of
`c23a`/`c23b` up to the `g = ln G` identification. -/

/-- S-part identity for the bridge:
`S(v) − S(v+d) = ln((2^v−1)²/((2^{v+d}−1)(2^{v−d}−1)))`. -/
theorem gapS_diff_eq {d v : ℝ}
    (h1 : (1:ℝ) < (2:ℝ)^v) (h2 : (1:ℝ) < (2:ℝ)^(v-d)) (h3 : (1:ℝ) < (2:ℝ)^(v+d)) :
    gapS d v - gapS d (v + d)
      = Real.log (((2:ℝ)^v - 1)^2 / (((2:ℝ)^(v+d) - 1) * ((2:ℝ)^(v-d) - 1))) := by
  have e : (v + d) - d = v := by ring
  unfold gapS
  rw [e]
  have p1 : (0:ℝ) < ((2:ℝ)^v - 1) / ((2:ℝ)^(v-d) - 1) :=
    div_pos (by linarith) (by linarith)
  have p2 : (0:ℝ) < ((2:ℝ)^(v+d) - 1) / ((2:ℝ)^v - 1) :=
    div_pos (by linarith) (by linarith)
  rw [← Real.log_div (ne_of_gt p1) (ne_of_gt p2)]
  congr 1
  have n1 : ((2:ℝ)^v - 1) ≠ 0 := ne_of_gt (by linarith)
  have n2 : ((2:ℝ)^(v-d) - 1) ≠ 0 := ne_of_gt (by linarith)
  have n3 : ((2:ℝ)^(v+d) - 1) ≠ 0 := ne_of_gt (by linarith)
  have n4 : ((2:ℝ)^(v+d) - 1) / ((2:ℝ)^v - 1) ≠ 0 := ne_of_gt p2
  have n5 : ((2:ℝ)^v - 1) / ((2:ℝ)^(v-d) - 1) ≠ 0 := ne_of_gt p1
  field_simp

/-- T-part identity for the bridge: `T(m) − T(m−1) = ln(1−(q′/Q_m)²)`,
using `Q_{m−1} = Q_m − q′` (i.e. `Q_{t+1} = Q_t + q′`). -/
theorem gapT_diff_eq {qp qpp m : ℝ}
    (hqp : 0 < qp)
    (hQm : (0:ℝ) < gapQ qp qpp m) (hQm1 : (0:ℝ) < gapQ qp qpp (m-1)) :
    gapT qp qpp m - gapT qp qpp (m-1) = Real.log (1 - (qp/gapQ qp qpp m)^2) := by
  have hQrel : gapQ qp qpp (m-1) = gapQ qp qpp m - qp := by unfold gapQ; ring
  have n1 : gapQ qp qpp m ≠ 0 := ne_of_gt hQm
  have n1' : (0:ℝ) < gapQ qp qpp m + qp := by linarith [hQm, hqp]
  have n2 : gapQ qp qpp (m-1) ≠ 0 := ne_of_gt hQm1
  -- single-fraction forms
  have e1 : (1:ℝ) + qp / gapQ qp qpp m = (gapQ qp qpp m + qp) / gapQ qp qpp m := by
    rw [add_div, div_self n1]
  have e2 : (1:ℝ) + qp / gapQ qp qpp (m-1) = gapQ qp qpp m / gapQ qp qpp (m-1) := by
    have hQm1eq : gapQ qp qpp m = gapQ qp qpp (m-1) + qp := by linarith [hQrel]
    calc (1:ℝ) + qp / gapQ qp qpp (m-1)
        = (gapQ qp qpp (m-1) + qp) / gapQ qp qpp (m-1) := by rw [add_div, div_self n2]
      _ = gapQ qp qpp m / gapQ qp qpp (m-1) := by rw [hQm1eq]
  have e3 : (1:ℝ) - (qp / gapQ qp qpp m)^2
      = (gapQ qp qpp (m-1) * (gapQ qp qpp m + qp)) / (gapQ qp qpp m)^2 := by
    rw [hQrel]
    field_simp
    ring
  rw [show gapT qp qpp m - gapT qp qpp (m-1)
      = Real.log (1 + qp / gapQ qp qpp m) - Real.log (1 + qp / gapQ qp qpp (m-1)) from rfl,
    e1, e2, e3,
    Real.log_div (ne_of_gt n1') n1, Real.log_div n1 n2,
    Real.log_div (mul_ne_zero n2 (ne_of_gt n1')) (pow_ne_zero 2 n1),
    Real.log_mul n2 (ne_of_gt n1'), pow_two, Real.log_mul n1 n1]
  ring

/-- Bridge `gapDelta = gapDeltaLog`: the exact algebra identifying
`gapDelta qp qpp (2m) d e (m−1)` (T-diff + S-diff) with the criterion's
log-sum `gapDeltaLog qp qpp d e m`. Closes the `hdelta` hypothesis of
`c23a`/`c23b` up to the `g = ln G` identification. -/
theorem gapDelta_gapDeltaLog {qp qpp d e : ℝ} {m : ℕ}
    (hqp : 0 < qp) (hqpp : 0 < qpp) (hd : 0 < d) (he : 0 < e)
    (hm : 1 ≤ m) :
    gapDelta qp qpp (2*(m:ℝ)) d e ((m:ℝ)-1) = gapDeltaLog qp qpp d e (m:ℝ) := by
  have hM : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hQm : (0:ℝ) < gapQ qp qpp (m:ℝ) := by
    unfold gapQ
    have h1 : (0:ℝ) ≤ (m:ℝ) * qp := mul_nonneg (by linarith) (le_of_lt hqp)
    linarith [hqpp]
  have hQm1 : (0:ℝ) < gapQ qp qpp ((m:ℝ)-1) := by
    unfold gapQ
    have h1 : (0:ℝ) ≤ ((m:ℝ)-1) * qp := mul_nonneg (by linarith) (le_of_lt hqp)
    linarith [hqpp]
  have hxm : gapx (2*(m:ℝ)) d e (m:ℝ) = (m:ℝ)*d + e := by unfold gapx; ring
  have hv : (0:ℝ) < gapx (2*(m:ℝ)) d e (m:ℝ) := by
    rw [hxm]; nlinarith [hd, he, hM]
  have hvd : (0:ℝ) < gapx (2*(m:ℝ)) d e (m:ℝ) - d := by
    rw [hxm]
    have hmd : (1:ℝ)*d ≤ (m:ℝ)*d := mul_le_mul_of_nonneg_right hM (le_of_lt hd)
    linarith [he]
  have hS1 : (1:ℝ) < (2:ℝ)^(gapx (2*(m:ℝ)) d e (m:ℝ)) := by
    calc (1:ℝ) = (2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
      _ < (2:ℝ)^(gapx (2*(m:ℝ)) d e (m:ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hv
  have hS2 : (1:ℝ) < (2:ℝ)^(gapx (2*(m:ℝ)) d e (m:ℝ) - d) := by
    calc (1:ℝ) = (2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
      _ < (2:ℝ)^(gapx (2*(m:ℝ)) d e (m:ℝ) - d) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hvd
  have hS3 : (1:ℝ) < (2:ℝ)^(gapx (2*(m:ℝ)) d e (m:ℝ) + d) := by
    calc (1:ℝ) = (2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
      _ < (2:ℝ)^(gapx (2*(m:ℝ)) d e (m:ℝ) + d) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith [hv, hd])
  have hu1 : gapu (2*(m:ℝ)) d e (m:ℝ) = gapx (2*(m:ℝ)) d e (m:ℝ) := by
    unfold gapu gapx; ring
  have hu2 : gapu (2*(m:ℝ)) d e ((m:ℝ)-1) = gapx (2*(m:ℝ)) d e (m:ℝ) + d := by
    unfold gapu gapx; ring
  have hS := gapS_diff_eq hS1 hS2 hS3
  have hT := gapT_diff_eq (m := (m:ℝ)) hqp hQm hQm1
  have hdelta : gapDelta qp qpp (2*(m:ℝ)) d e ((m:ℝ)-1)
      = (gapT qp qpp (m:ℝ) - gapT qp qpp ((m:ℝ)-1))
        + (gapS d (gapx (2*(m:ℝ)) d e (m:ℝ)) - gapS d (gapx (2*(m:ℝ)) d e (m:ℝ) + d)) := by
    unfold gapDelta
    have e1 : ((m:ℝ)-1) + 1 = (m:ℝ) := by ring
    rw [e1, hu1, hu2]
  have hlog : gapDeltaLog qp qpp d e (m:ℝ)
      = Real.log (1 - (qp / gapQ qp qpp (m:ℝ))^2) +
        Real.log (((2:ℝ)^(gapx (2*(m:ℝ)) d e (m:ℝ)) - 1)^2 /
          (((2:ℝ)^(gapx (2*(m:ℝ)) d e (m:ℝ) + d) - 1)
            * ((2:ℝ)^(gapx (2*(m:ℝ)) d e (m:ℝ) - d) - 1))) := rfl
  rw [hdelta, hT, hS, hlog]

end GapCF
