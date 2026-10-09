import Mathproofs.CollatzGapCF

/-!
# C24 Lemma 3: finite first-difference rule (R77 — machine-checked)

Hand proof: `~/workspace/math-unsolved/c24_proofs_r30.md`, Lemma 3 ([PROVED*]).

For irrational `α`, file-index `n : ℕ` (= hand block-index `m = n + 2`):
- `T = cquot α (n + 3)` (the CF tail `[A(n+3); A(n+4), …]`),
- `M = Q α (n + 1) / Q α n` (the reversed head `[A(n+1); …, A(1)]`).

`T ≠ M` always (already [PROVED] as `cf_selector_ne`: `T` irrational,
`M` rational), and `sgn(T - M)` is decided by the first `j ∈ {0, …, n}`
with `A α (n+3+j) ≠ A α (n+1-j)`:
  `sgn(T - M) = (-1)^j * sgn(A α (n+3+j) - A α (n+1-j))`.
If all `n + 1` pairs agree, `sgn(T - M) = (-1)^n`.

Formalization strategy (avoids building a general finite-CF evaluator
or Möbius/determinant machinery): recursive one-step reduction.
At "level" `j` (`0 ≤ j ≤ n`):
  `T_j = cquot α (n+3+j)`, `M_j = Q α (n+1-j) / Q α (n-j)`.
- Split: `T_j = A(n+3+j) + t_j` with `t_j = 1 / cquot(n+4+j) ∈ (0,1)`
  (via `cquot_gt_one`);
  `M_j = A(n+1-j) + m_j` with `m_j = Q(n-j-1) / Q(n-j) ∈ (0,1]` for `j < n`
  (via `Q_mono`); at the bottom `j = n`, `M_n = A 1` exactly.
- Difference decides: if `A(n+3+j) ≠ A(n+1-j)` then the partial quotients
  are integers with `|A-diff| ≥ 1 > |t_j - m_j|`, so
  `sgn(T_j - M_j) = sgn(A-diff)` (`cf_firstdiff_decide`).
- Agreement flips: if equal (and `j < n`) then
  `T_j - M_j = t_j - m_j`, and reciprocals reverse the comparison:
  `sgn(T_j - M_j) = -sgn(T_{j+1} - M_{j+1})` (`cf_firstdiff_flip`).
- Bottom (`j = n`): `M_n = Q 1 / Q 0 = A 1` exactly, and
  `T_n - M_n = (A(2n+3) - A(1)) + t_n` with `t_n ∈ (0,1)`
  (`cf_firstdiff_term`).
Induction on `j` assembles the rule (`cf_firstdiff_gen`, `cf_firstdiff`).
All steps are elementary order manipulations on top of
`CollatzGapCF.lean`'s API.

Checked with Lean 4.34.1 + Mathlib v4.34.1 on xavier, zero sorrys;
`#print axioms` on the three main theorems is standard-only
(see `lean/AxProbeC24.lean`).
-/

namespace GapCF

variable {α : ℝ}

/-- Supporting: complete quotient splits into partial quotient
plus reciprocal tail. From `cquot_mul_fract`: the fractional part is
exactly the reciprocal of the next complete quotient. -/
theorem cquot_split (hirr : Irrational α) (k : ℕ) :
    cquot α k = A α k + (cquot α (k + 1))⁻¹ := by
  have hmul := cquot_mul_fract hirr k
  have hdiff : cquot α k - A α k = (cquot α (k + 1))⁻¹ :=
    eq_inv_of_mul_eq_one_right hmul
  have hsplit : cquot α k = A α k + (cquot α k - A α k) := by ring
  rw [hdiff] at hsplit
  exact hsplit

/-- Supporting: convergent-denominator ratio splits off its head
partial quotient. From `Q_rec` at `i - 1` divided by `Q i > 0`. -/
theorem Qratio_split (hirr : Irrational α) (i : ℕ) (hi : 1 ≤ i) :
    Q α (i + 1) / Q α i = A α (i + 1) + Q α (i - 1) / Q α i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hQ : Q α (j + 1) ≠ 0 := ne_of_gt (Q_pos hirr (j + 1))
  have h1 : j + 1 + 1 = j + 2 := by omega
  have h2 : j + 1 - 1 = j := by omega
  rw [h1, h2, Q_rec (α := α) j, add_div, mul_div_cancel_right₀ _ hQ]

/-- Supporting: `Q` is monotone nondecreasing. From `Q_rec`:
`Q(k+2) = A(k+2) * Q(k+1) + Q(k) ≥ Q(k+1)` via `pquot_ge_one`,
`Q_pos`; base case `Q 0 = 1 ≤ A 1 = Q 1` via `Q_zero`, `Q_one`. -/
theorem Q_mono (hirr : Irrational α) (k : ℕ) : Q α k ≤ Q α (k + 1) := by
  cases k with
  | zero =>
    rw [Q_zero, Q_one]
    have h := pquot_ge_one hirr 0
    simp only [A]
    exact_mod_cast h
  | succ j =>
    show Q α (j + 1) ≤ Q α (j + 2)
    have hrec := Q_rec (α := α) j
    have hA : (1:ℝ) ≤ A α (j + 2) := by
      have h := pquot_ge_one hirr (j + 1)
      have heq : j + 1 + 1 = j + 2 := by omega
      rw [heq] at h
      simp only [A]
      exact_mod_cast h
    have hQ1 : (0:ℝ) ≤ Q α (j + 1) := le_of_lt (Q_pos hirr (j + 1))
    have hQj : (0:ℝ) ≤ Q α j := le_of_lt (Q_pos hirr j)
    rw [hrec]
    have hmul := mul_le_mul_of_nonneg_right hA hQ1
    linarith

/-- C24 Lemma 3a: one-step reduction — agreement at level `j`
flips the comparison to level `j + 1`.
`T_j - M_j = t_j - m_j` with `t_j, m_j > 0`; hence
`sgn(T_j - M_j) = -sgn(1/t_j - 1/m_j) = -sgn(T_{j+1} - M_{j+1})`. -/
theorem cf_firstdiff_flip (hirr : Irrational α) (n j : ℕ) (hj : j + 1 ≤ n)
    (hagree : A α (n + 3 + j) = A α (n + 1 - j)) :
    ((cquot α (n + 3 + j) < Q α (n + 1 - j) / Q α (n - j)) ↔
      (Q α (n - j) / Q α (n - j - 1) < cquot α (n + 4 + j))) ∧
    ((Q α (n + 1 - j) / Q α (n - j) < cquot α (n + 3 + j)) ↔
      (cquot α (n + 4 + j) < Q α (n - j) / Q α (n - j - 1))) := by
  have hTs := cquot_split hirr (n + 3 + j)
  have hle : 1 ≤ n - j := by omega
  have hMs := Qratio_split hirr (n - j) hle
  have e1 : n - j + 1 = n + 1 - j := by omega
  have e2 : n + 3 + j + 1 = n + 4 + j := by omega
  rw [e1] at hMs
  rw [e2] at hTs
  rw [hagree] at hTs
  have ht : (0:ℝ) < (cquot α (n + 4 + j))⁻¹ := by
    rw [← e2]
    exact inv_pos.mpr (cquot_pos hirr (n + 3 + j))
  have hm : (0:ℝ) < Q α (n - j - 1) / Q α (n - j) :=
    div_pos (Q_pos hirr _) (Q_pos hirr _)
  constructor
  · rw [hTs, hMs, add_lt_add_iff_left, ← inv_lt_inv₀ hm ht, inv_inv, inv_div]
  · rw [hTs, hMs, add_lt_add_iff_left, ← inv_lt_inv₀ ht hm, inv_inv, inv_div]

/-- Pure order lemma behind `cf_firstdiff_decide`: if `T = u + t`,
`M = v + m` with `t ∈ (0,1)`, `m ∈ [0,1]`, and `u ≠ v` integers,
then the integer parts decide both comparisons. -/
theorem firstdiff_decide_of_splits {u v : ℤ} {t m T M : ℝ}
    (hT : T = (u : ℝ) + t) (hM : M = (v : ℝ) + m)
    (ht0 : 0 < t) (ht1 : t < 1) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hne : u ≠ v) :
    (T < M ↔ (u : ℝ) < (v : ℝ)) ∧ (M < T ↔ (v : ℝ) < (u : ℝ)) := by
  have hUV : (u : ℝ) ≠ (v : ℝ) := fun h => hne (by exact_mod_cast h)
  have step : ∀ a b : ℤ, (a : ℝ) < (b : ℝ) → (a : ℝ) + 1 ≤ (b : ℝ) := by
    intro a b hab
    have h1 : a + 1 ≤ b := Int.add_one_le_of_lt (Int.cast_lt.mp hab)
    exact_mod_cast h1
  constructor
  · constructor
    · intro hTM
      rcases lt_trichotomy (u : ℝ) (v : ℝ) with huv | huv | hvu
      · exact huv
      · exact absurd huv hUV
      · exfalso
        have hle := step v u hvu
        rw [hT, hM] at hTM
        linarith
    · intro huv
      have hle := step u v huv
      rw [hT, hM]
      linarith
  · constructor
    · intro hMT
      rcases lt_trichotomy (v : ℝ) (u : ℝ) with hvu | hvu | huv
      · exact hvu
      · exact absurd hvu.symm hUV
      · exfalso
        have hle := step u v huv
        rw [hT, hM] at hMT
        linarith
    · intro hvu
      have hle := step v u hvu
      rw [hT, hM]
      linarith

/-- C24 Lemma 3b: one-step reduction — difference at level `j`
decides the comparison outright. `|A-diff| ≥ 1 > |t_j - m_j|`
(`t_j ∈ (0,1)`, `m_j ∈ [0,1]`), so the integer difference dominates.
The bottom case `j = n` is handled separately (`M_n = A 1` exactly). -/
theorem cf_firstdiff_decide (hirr : Irrational α) (n j : ℕ) (hj : j ≤ n)
    (hdiff : A α (n + 3 + j) ≠ A α (n + 1 - j)) :
    ((cquot α (n + 3 + j) < Q α (n + 1 - j) / Q α (n - j)) ↔
      (A α (n + 3 + j) < A α (n + 1 - j))) ∧
    ((Q α (n + 1 - j) / Q α (n - j) < cquot α (n + 3 + j)) ↔
      (A α (n + 1 - j) < A α (n + 3 + j))) := by
  have hT := cquot_split hirr (n + 3 + j)
  have eT : n + 3 + j + 1 = n + 4 + j := by omega
  rw [eT] at hT
  have htc : (1:ℝ) < cquot α (n + 4 + j) := by
    have h := cquot_gt_one hirr (n + 3 + j)
    rwa [show n + 3 + j + 1 = n + 4 + j by omega] at h
  have ht0 : (0:ℝ) < (cquot α (n + 4 + j))⁻¹ :=
    inv_pos.mpr (lt_trans zero_lt_one htc)
  have ht1 : (cquot α (n + 4 + j))⁻¹ < (1:ℝ) := inv_lt_one_of_one_lt₀ htc
  have hne : pquot α (n + 3 + j) ≠ pquot α (n + 1 - j) := by
    intro hcon
    apply hdiff
    show ((pquot α (n + 3 + j) : ℤ) : ℝ) = ((pquot α (n + 1 - j) : ℤ) : ℝ)
    rw [hcon]
  rcases eq_or_lt_of_le hj with hjeq | hlt
  · have h2 : n = j := hjeq.symm
    subst h2
    -- bottom case `j = n`: `M_n = A 1` exactly
    have e1 : n + 1 - n = 1 := by omega
    have e0 : n - n = 0 := by omega
    have hM : Q α (n + 1 - n) / Q α (n - n)
        = (((pquot α (n + 1 - n) : ℤ)) : ℝ) + 0 := by
      rw [e1, e0, Q_one, Q_zero, div_one]
      simp [A]
    have key := firstdiff_decide_of_splits (u := pquot α (n + 3 + n))
      (v := pquot α (n + 1 - n)) (t := (cquot α (n + 4 + n))⁻¹) (m := (0 : ℝ))
      (T := cquot α (n + 3 + n)) (M := Q α (n + 1 - n) / Q α (n - n))
      hT hM ht0 ht1 (le_refl (0 : ℝ)) zero_le_one hne
    exact key
  · -- `j < n`: split `M_j`
    have hM0 := Qratio_split hirr (n - j) (by omega : 1 ≤ n - j)
    have eM : n - j + 1 = n + 1 - j := by omega
    rw [eM] at hM0
    have hm0 : (0:ℝ) ≤ Q α (n - j - 1) / Q α (n - j) :=
      le_of_lt (div_pos (Q_pos hirr _) (Q_pos hirr _))
    have hm1 : Q α (n - j - 1) / Q α (n - j) ≤ (1:ℝ) := by
      rw [div_le_one (Q_pos hirr _)]
      have h := Q_mono hirr (n - j - 1)
      rwa [show n - j - 1 + 1 = n - j by omega] at h
    have key := firstdiff_decide_of_splits (u := pquot α (n + 3 + j))
      (v := pquot α (n + 1 - j)) (t := (cquot α (n + 4 + j))⁻¹)
      (m := Q α (n - j - 1) / Q α (n - j))
      (T := cquot α (n + 3 + j)) (M := Q α (n + 1 - j) / Q α (n - j))
      hT hM0 ht0 ht1 hm0 hm1 hne
    exact key

/-- Even/odd swap for the sign bookkeeping in the induction:
flipping once swaps the two branches of the `Even j` split. -/
theorem if_even_succ_swap (j : ℕ) (p q : Prop) [Decidable p] [Decidable q] :
    (if Even j then p else q) ↔ (if Even (j + 1) then q else p) := by
  by_cases hev : Even j
  · have h2 : ¬ Even (j + 1) := Nat.even_add_one.not.mpr (not_not_intro hev)
    rw [ite_eq_left hev, ite_eq_right h2]
  · have h2 : Even (j + 1) := Nat.even_add_one.mpr hev
    rw [ite_eq_right hev, ite_eq_left h2]

/-- Generalized first-difference rule: the comparison at an arbitrary
starting level `k`, with the first difference at level `k + j`.
Induction on `j`: the base case is `cf_firstdiff_decide` at level `k`;
the step flips once via `cf_firstdiff_flip` and applies the IH at `k+1`. -/
theorem cf_firstdiff_gen (hirr : Irrational α) (n : ℕ) :
    ∀ (k j : ℕ), k + j ≤ n →
    (∀ i, i < j → A α (n + 3 + (k + i)) = A α (n + 1 - (k + i))) →
    (A α (n + 3 + (k + j)) ≠ A α (n + 1 - (k + j))) →
    ((cquot α (n + 3 + k) < Q α (n + 1 - k) / Q α (n - k)) ↔
      (if Even j then A α (n + 3 + (k + j)) < A α (n + 1 - (k + j))
       else A α (n + 1 - (k + j)) < A α (n + 3 + (k + j)))) ∧
    ((Q α (n + 1 - k) / Q α (n - k) < cquot α (n + 3 + k)) ↔
      (if Even j then A α (n + 1 - (k + j)) < A α (n + 3 + (k + j))
       else A α (n + 3 + (k + j)) < A α (n + 1 - (k + j)))) := by
  intro k j
  induction j generalizing k with
  | zero =>
    intro hkj hagree hdiff
    have hdec := cf_firstdiff_decide hirr n k (by omega) (by simpa using hdiff)
    have hev0 : Even (0 : ℕ) := ⟨0, rfl⟩
    simp only [hev0, ite_true] at ⊢
    exact hdec
  | succ j ih =>
    intro hkj hagree hdiff
    have hkj1 : k + 1 ≤ n := by omega
    have hag0 : A α (n + 3 + k) = A α (n + 1 - k) := hagree 0 (by omega)
    obtain ⟨hflip1, hflip2⟩ := cf_firstdiff_flip hirr n k hkj1 hag0
    have eM1 : n + 1 - (k + 1) = n - k := by omega
    have eM2 : n - (k + 1) = n - k - 1 := by omega
    have eT1 : n + 3 + (k + 1) = n + 4 + k := by omega
    have eA1 : n + 3 + ((k + 1) + j) = n + 3 + (k + (j + 1)) := by omega
    have eA2 : n + 1 - ((k + 1) + j) = n + 1 - (k + (j + 1)) := by omega
    have ihk := ih (k + 1) (by omega)
      (fun i hi => by
        have h := hagree (i + 1) (by omega)
        have e : k + (i + 1) = (k + 1) + i := by omega
        rwa [e] at h)
      (by
        have e : k + (j + 1) = (k + 1) + j := by omega
        rwa [e] at hdiff)
    rw [eM1, eM2, eT1, eA1, eA2] at ihk
    constructor
    · rw [hflip1, ihk.2, if_even_succ_swap]
    · rw [hflip2, ihk.1, if_even_succ_swap]

/-- C24 Lemma 3: first-difference decision rule. The `k = 0` case of
`cf_firstdiff_gen`: each agreement flip contributes one sign reversal,
hence the `Even`/`Odd` case split. -/
theorem cf_firstdiff (hirr : Irrational α) (n j : ℕ) (hj : j ≤ n)
    (hagree : ∀ i, i < j → A α (n + 3 + i) = A α (n + 1 - i))
    (hdiff : A α (n + 3 + j) ≠ A α (n + 1 - j)) :
    ((cquot α (n + 3) < Q α (n + 1) / Q α n) ↔
      (if Even j then A α (n + 3 + j) < A α (n + 1 - j)
       else A α (n + 1 - j) < A α (n + 3 + j))) ∧
    ((Q α (n + 1) / Q α n < cquot α (n + 3)) ↔
      (if Even j then A α (n + 1 - j) < A α (n + 3 + j)
       else A α (n + 3 + j) < A α (n + 1 - j))) := by
  have h := cf_firstdiff_gen hirr n 0 j (by omega)
    (fun i hi => by simpa using hagree i hi)
    (by simpa using hdiff)
  simpa using h

/-- Auxiliary: applying the flip `k` times moves the comparison from
level `0` to level `k`, toggling the direction at each step. -/
theorem cf_firstdiff_term_aux (hirr : Irrational α) (n : ℕ)
    (hagree : ∀ j, j ≤ n → A α (n + 3 + j) = A α (n + 1 - j)) :
    ∀ k, k ≤ n →
    ((cquot α (n + 3) < Q α (n + 1) / Q α n) ↔
      (if Even k then cquot α (n + 3 + k) < Q α (n + 1 - k) / Q α (n - k)
       else Q α (n + 1 - k) / Q α (n - k) < cquot α (n + 3 + k))) ∧
    ((Q α (n + 1) / Q α n < cquot α (n + 3)) ↔
      (if Even k then Q α (n + 1 - k) / Q α (n - k) < cquot α (n + 3 + k)
       else cquot α (n + 3 + k) < Q α (n + 1 - k) / Q α (n - k))) := by
  intro k
  induction k with
  | zero =>
    intro _
    have hev0 : Even (0 : ℕ) := ⟨0, rfl⟩
    simp only [hev0, ite_true, add_zero, Nat.sub_zero]
    exact ⟨trivial, trivial⟩
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    have hflip := cf_firstdiff_flip hirr n k hk (hagree k (by omega))
    have eM1 : n + 1 - (k + 1) = n - k := by omega
    have eM2 : n - (k + 1) = n - k - 1 := by omega
    have eT1 : n + 3 + (k + 1) = n + 4 + k := by omega
    rw [eM1, eM2, eT1]
    constructor
    · rw [ihk.1, hflip.1, hflip.2, if_even_succ_swap]
    · rw [ihk.2, hflip.2, hflip.1, if_even_succ_swap]

/-- C24 Lemma 3: termination case. If all `n + 1` head terms agree,
the bottom level gives `T_n - M_n = t_n > 0` (since `M_n = A 1` exactly
and the last agreement forces `A(2n+3) = A 1`), so after `n` flips
`sgn(T - M) = (-1)^n`: `T < M ↔ Odd n`, `M < T ↔ Even n`. -/
theorem cf_firstdiff_term (hirr : Irrational α) (n : ℕ)
    (hagree : ∀ j, j ≤ n → A α (n + 3 + j) = A α (n + 1 - j)) :
    ((cquot α (n + 3) < Q α (n + 1) / Q α n) ↔ Odd n) ∧
    ((Q α (n + 1) / Q α n < cquot α (n + 3)) ↔ Even n) := by
  have haux := cf_firstdiff_term_aux hirr n hagree n (le_refl n)
  have e1 : n + 1 - n = 1 := by omega
  have hM : Q α (n + 1 - n) / Q α (n - n) = A α 1 := by
    have e0 : n - n = 0 := by omega
    rw [e1, e0, Q_one, Q_zero, div_one]
  have hT := cquot_split hirr (n + 3 + n)
  have eT : n + 3 + n + 1 = n + 4 + n := by omega
  rw [eT] at hT
  have htc : (1:ℝ) < cquot α (n + 4 + n) := by
    have h := cquot_gt_one hirr (n + 3 + n)
    rwa [show n + 3 + n + 1 = n + 4 + n by omega] at h
  have ht0 : (0:ℝ) < (cquot α (n + 4 + n))⁻¹ :=
    inv_pos.mpr (lt_trans zero_lt_one htc)
  have hag_n := hagree n (le_refl n)
  rw [e1] at hag_n
  have hgt : Q α (n + 1 - n) / Q α (n - n) < cquot α (n + 3 + n) := by
    rw [hM, hT, hag_n]
    linarith
  have hnge : ¬ cquot α (n + 3 + n) < Q α (n + 1 - n) / Q α (n - n) :=
    not_lt_of_gt hgt
  have key1 : ((if Even n then cquot α (n + 3 + n) < Q α (n + 1 - n) / Q α (n - n)
      else Q α (n + 1 - n) / Q α (n - n) < cquot α (n + 3 + n)) ↔ Odd n) := by
    by_cases hev : Even n
    · simp only [hev, ite_true]
      rw [iff_false_intro hnge]
      exact (iff_false_intro fun hodd => (Nat.not_even_iff_odd.mpr hodd) hev).symm
    · simp only [hev, ite_false]
      rw [iff_true_intro hgt]
      exact (iff_true_intro ((Nat.not_even_iff_odd).mp hev)).symm
  have key2 : ((if Even n then Q α (n + 1 - n) / Q α (n - n) < cquot α (n + 3 + n)
      else cquot α (n + 3 + n) < Q α (n + 1 - n) / Q α (n - n)) ↔ Even n) := by
    by_cases hev : Even n
    · rw [ite_eq_left hev]
      exact iff_of_true hgt hev
    · rw [ite_eq_right hev]
      exact iff_of_false hnge hev
  exact ⟨haux.1.trans key1, haux.2.trans key2⟩

end GapCF
