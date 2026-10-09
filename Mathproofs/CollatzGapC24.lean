import Mathproofs.CollatzGapCF

/-!
# C24 Lemma 2: the tail-mirror selector (R61 draft; R69 index fix)

Source proof: `~/workspace/math-unsolved/c24_proofs_r30.md` (Round 30).
Builds on the verified C24 Lemma 1 (`GapCF.cf_ratio_formula`, `GapCF.cf_error_formula`)
in `Mathproofs/CollatzGapCF.lean`.

For irrational `α`, at hand block-index `m ≥ 2`:
- `ρ := |e_m| / |e_{m-1}|` (the gap-ratio selector input; `e_k = α * q_k - p_k`),
- `r := q_{m-2} / q_{m-1}` (the convergent-denominator ratio),
- `T := α_{m+1} = cquot α (m+1)` (the CF tail),
- `M := q_{m-1} / q_{m-2}` (the reversed-head value).

**Lemma 2**: `ρ ⋚ r ↔ T ⋛ M` (reciprocals reverse the comparison),
all quantities strictly positive.

In Lean indices, file-index `n : ℕ` is hand block-index `m = n + 2`
(the hand proof used `m ≥ 2`):
- `cf_selector_le`: `|cerr α (n+2)| / |cerr α (n+1)| ≤ Q α n / Q α (n+1) ↔
   Q α (n+1) / Q α n ≤ cquot α (n+3)`,
- `cf_selector_lt`: strict version `< ↔ >`,
- `cf_selector_eq`: `ρ = r ↔ T = M`.

All via `cf_ratio_formula` (`ρ = 1 / T`) plus elementary positivity
manipulation; zero Diophantine input.

**R69 correction**: R61's draft stated
`|cerr (n+1)| / |cerr n| ≤ Q n / Q (n+1) ↔ Q (n+1) / Q n ≤ cquot (n+2)`.
That biconditional is true, but it pairs `ρ_{n+1} = |e_{n+1}| / |e_n|`
with `r_{n+2} = q_n / q_{n+1}` — off by one. C23's selector at block `m`
is `(ρ_m, r_m) = (δ_m / δ_{m-1}, q_{m-2} / q_{m-1})` (primary source:
`c23_proofs_r27.md`, l.8; the `q_n = q'(a + r)` step of C23's proof is
load-bearing on this exact `r`). The two `r`'s are genuinely different
comparisons: e.g. for `α = log₂3` at hand-index `n = 3`,
`sgn(ρ₃ - q₁/q₂) = -1` but `sgn(ρ₃ - q₂/q₃) = +1` (exact integer
arithmetic). R61's version therefore did not decide C23's selector.
Fixed here by shifting the `cerr` / `cquot` indices up by one; the
`Q`-ratio was already the correct `r_{n+2}`.
-/

namespace GapCF

variable {α : ℝ}

/-- C24 Lemma 2 (non-strict): `ρ ≤ r ↔ M ≤ T`. -/
theorem cf_selector_le (hirr : Irrational α) (n : ℕ) :
    |cerr α (n + 2)| / |cerr α (n + 1)| ≤ Q α n / Q α (n + 1) ↔
    Q α (n + 1) / Q α n ≤ cquot α (n + 3) := by
  have hQn : (0:ℝ) < Q α n := Q_pos hirr n
  have hQn1 : (0:ℝ) < Q α (n + 1) := Q_pos hirr (n + 1)
  have hT : (0:ℝ) < cquot α (n + 3) := cquot_pos hirr (n + 2)
  rw [cf_ratio_formula hirr (n + 1), div_le_div_iff₀ hT hQn1, div_le_iff₀ hQn,
    mul_comm (Q α n) (cquot α (n + 3)), one_mul]

/-- C24 Lemma 2 (strict): `ρ < r ↔ M < T` — the comparison reverses
for strict inequalities. -/
theorem cf_selector_lt (hirr : Irrational α) (n : ℕ) :
    |cerr α (n + 2)| / |cerr α (n + 1)| < Q α n / Q α (n + 1) ↔
    Q α (n + 1) / Q α n < cquot α (n + 3) := by
  have hQn : (0:ℝ) < Q α n := Q_pos hirr n
  have hQn1 : (0:ℝ) < Q α (n + 1) := Q_pos hirr (n + 1)
  have hT : (0:ℝ) < cquot α (n + 3) := cquot_pos hirr (n + 2)
  rw [cf_ratio_formula hirr (n + 1), div_lt_div_iff₀ hT hQn1, div_lt_iff₀ hQn,
    mul_comm (Q α n) (cquot α (n + 3)), one_mul]

/-- C24 Lemma 2 (equality): `ρ = r ↔ T = M`.
Combined with `cquot_irr` (`T` irrational) and `M` rational, this is the
boundary case that never occurs (C24 Corollary: strict dichotomy). -/
theorem cf_selector_eq (hirr : Irrational α) (n : ℕ) :
    |cerr α (n + 2)| / |cerr α (n + 1)| = Q α n / Q α (n + 1) ↔
    cquot α (n + 3) = Q α (n + 1) / Q α n := by
  have hQn : (0:ℝ) < Q α n := Q_pos hirr n
  have hQn1 : (0:ℝ) < Q α (n + 1) := Q_pos hirr (n + 1)
  have hT : (0:ℝ) < cquot α (n + 3) := cquot_pos hirr (n + 2)
  have hQne : Q α n ≠ 0 := ne_of_gt hQn
  rw [cf_ratio_formula hirr (n + 1)]
  constructor
  · intro h
    rw [div_eq_div_iff (ne_of_gt hT) (ne_of_gt hQn1), one_mul] at h
    rw [eq_div_iff hQne, mul_comm (cquot α (n + 3)) (Q α n)]
    exact h.symm
  · intro h
    rw [div_eq_div_iff (ne_of_gt hT) (ne_of_gt hQn1), h, one_mul]
    field_simp

/-- C24 strict dichotomy: `ρ ≠ r` always (`T` irrational, `M` rational),
so C23's split has no boundary case. -/
theorem cf_selector_ne (hirr : Irrational α) (n : ℕ) :
    |cerr α (n + 2)| / |cerr α (n + 1)| ≠ Q α n / Q α (n + 1) := by
  intro h
  have heq := (cf_selector_eq hirr n).mp h
  have hirrT : Irrational (cquot α (n + 3)) := cquot_irr hirr (n + 3)
  rw [heq] at hirrT
  have hne := (irrational_iff_ne_rational _).mp hirrT (cden α (n + 1)) (cden α n)
    (ne_of_gt (cden_pos hirr n))
  apply hne
  rfl

end GapCF
