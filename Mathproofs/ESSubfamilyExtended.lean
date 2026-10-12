/-
  ESSubfamilyExtended.lean — R245 generalized sub-family theorem + staged extensions (R253 admission criterion, R261 A₀-constancy, R265 repaired split/layered).

  Paper: papers/subfamily-ladder-ceiling-October-11-2026/
  Status: [PROVED] — generalized_subfamily_identity. [PROVED*] (staged, machine-checked, review-cleared) — admission_criterion, a0_constancy, u_eq_Aqe_div_f, excess_prime_dvd_u, M_const, split_layered_restated, split_layered_repaired
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R262: exit 0 both sides, zero sorrys, axioms standard-only.
-/

/-
  ESSubfamilyExtended.lean — Lean formalization of R245's generalized
  sub-family theorem (Erdős–Straus parametric families, the r ∤ XSTEP′/q
  regime).

  Source: ~/workspace/math-unsolved/ROUND245_DOSSIER.md (Round 245, 2026-10-10).
  Rule-9 hostile review: ~/workspace/math-unsolved/review-r245-esext/
  (Codex gpt-6-astra / ultra) — SURVIVES under positive-integer parameter
  conventions, with two statement fixes applied here:
    (i)  positivity of A and r is now an explicit hypothesis (the reviewer
         exhibited a signed-parameter counterexample with C(0) = 0 when
         r < 0 is allowed);
    (ii) the "clean dichotomy" wording is not formalized (only the theorem).
  The R253 admission-criterion fold-in is DONE (R266, 2026-10-10): R253's
  rule-9 review returned SURVIVES (conditional on R245's integer setup,
  which this file supplies via hur/hf), formalized below as
  `admission_criterion` (+ `adm_congruence_solvable`). R261's constancy
  theorems are folded in below as well (rule-9 review: SURVIVES with the
  stronger formula A₀(m) = A/gcd(A,qe)); R261's unconditional ⟺ corollary
  is NOT formalized as stated (rule-9: false as written) — only its
  corrected restatement `split_layered_restated`.

  What is checked: for parameters satisfying R245's hypotheses (with the
  positivity fix), every s ≥ 1 in the shifted residue class
  s ≡ −m + 4qeV₀ (mod 4qeA₀) admits the explicit branch-1 identity
  4/(M′t+s) = 1/x + 1/(n·A·C) + 1/(B·C) for all t ≥ 0, with the closed forms
  from the dossier. The identity is proved directly (a slick relation chain),
  independent of R72's TFAE.

  Lean 4.34.1 / Mathlib (pin d13f23b723b8a846827a245b89c10fc7d3f11612).
  Zero sorrys. Standard axioms only.
-/

import Mathlib

namespace ESSubfamilyExtended

/-- R245 generalized sub-family theorem, with the rule-9 positivity fix
    (A, r > 0 explicit). -/
theorem generalized_subfamily_identity
    (q A r e f u m k V₀ s : ℤ)
    (S Mp : ℤ)
    (hq : 0 < q) (hA : 0 < A) (hr : 0 < r) (he : 0 < e)
    (hfpos : 0 < f) (hm3 : 3 ≤ m) (hmod4 : m ≡ 3 [ZMOD 4])
    (hS : S = 510510 * q) (hM : Mp = 4 * S)
    (hAS : A ∣ S)
    (hur : u * r = A * S)
    (hf : f * S = r * q * e)
    (hk : m * k = 1 + 4 * u)
    (hV₀ : q * e * k * V₀ ≡ u [ZMOD A])
    (hs : s ≡ -m + 4 * q * e * V₀ [ZMOD 4 * q * e * (A / ((Int.gcd A (q*e*k) : ℕ) : ℤ))])
    (h1s : 1 ≤ s) :
    ∀ t : ℤ, 0 ≤ t →
      (4 : ℚ) / ((Mp * t + s : ℤ) : ℚ) =
        1 / ((S * t + q * e * ((s + m) / (4 * q * e)) : ℤ) : ℚ) +
        1 / (((Mp * t + s : ℤ) : ℚ) * A *
          (((S / A) * k * t + (s * k + 1) / (4 * A) : ℤ) : ℚ)) +
        1 / (((r * t + f * ((s + m) / (4 * q * e)) : ℤ) : ℚ) *
          (((S / A) * k * t + (s * k + 1) / (4 * A) : ℤ) : ℚ)) := by
  -- Basic positivity facts
  have hSpos : 0 < S := by rw [hS]; positivity
  have hMpos : 0 < Mp := by rw [hM]; positivity
  have h4qe : (0:ℤ) < 4 * q * e := by positivity
  have h4qene : (4:ℤ) * q * e ≠ 0 := ne_of_gt h4qe
  have hAne : (A:ℤ) ≠ 0 := ne_of_gt hA
  have h4Ane : (4:ℤ) * A ≠ 0 := by positivity
  have hSne : (S:ℤ) ≠ 0 := ne_of_gt hSpos
  -- u > 0 from u * r = A * S
  have pos_of_mul_pos {a b : ℤ} (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a := by
    by_contra hcon
    have hle : a ≤ 0 := le_of_not_gt hcon
    have h2 : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hb
    omega
  have hu : 0 < u := by
    have h1 : (0:ℤ) < u * r := by rw [hur]; positivity
    exact pos_of_mul_pos h1 hr.le
  -- k > 0 from m * k = 1 + 4u
  have hkpos : 0 < k := by
    have h1 : (0:ℤ) < m * k := by rw [hk]; nlinarith [hu]
    rw [mul_comm] at h1
    exact pos_of_mul_pos h1 (by omega)
  -- The gcd setup: g = gcd(A, qek), A₀ = A / g
  set g : ℕ := Int.gcd A (q * e * k) with hgdef
  set A₀ : ℤ := A / ((g : ℕ) : ℤ) with hA₀def
  have hgA : ((g : ℕ) : ℤ) ∣ A := Int.gcd_dvd_left A (q * e * k)
  have hgq : ((g : ℕ) : ℤ) ∣ q * e * k := Int.gcd_dvd_right A (q * e * k)
  have hgpos : 0 < g := by
    by_contra hcon
    have hle : g ≤ 0 := le_of_not_gt hcon
    have h0 : g = 0 := by omega
    have hA0 := hgA
    rw [h0] at hA0
    simp at hA0
    omega
  have hg1 : (1:ℤ) ≤ ((g : ℕ) : ℤ) := by exact_mod_cast hgpos
  have hAeq : A = A₀ * ((g : ℕ) : ℤ) := by
    rw [hA₀def]
    exact (Int.ediv_mul_cancel hgA).symm
  have hA₀pos : 0 < A₀ := by
    have h1 : (0:ℤ) < A₀ * ((g : ℕ) : ℤ) := by rw [← hAeq]; exact hA
    exact pos_of_mul_pos h1 (by exact_mod_cast Nat.zero_le g)
  -- V from 4qe ∣ s + m (via the residue class)
  have hs_dvd : (4:ℤ) * q * e * A₀ ∣ ((-m + 4 * q * e * V₀) - s) :=
    (Int.modEq_iff_dvd).mp hs
  obtain ⟨V, hV⟩ : (4:ℤ) * q * e ∣ (s + m) := by
    have h1 : (4:ℤ) * q * e ∣ (4 * q * e * A₀) := dvd_mul_right _ _
    have h2 : (4:ℤ) * q * e ∣ ((-m + 4 * q * e * V₀) - s) := dvd_trans h1 hs_dvd
    have h3 : (4:ℤ) * q * e ∣ (4 * q * e * V₀) := dvd_mul_right _ _
    have h4 : (4:ℤ) * q * e ∣ (((-m + 4 * q * e * V₀) - s) - 4 * q * e * V₀) :=
      dvd_sub h2 h3
    have heq : (((-m + 4 * q * e * V₀) - s) - 4 * q * e * V₀) = -(s + m) := by ring
    rwa [heq, dvd_neg] at h4
  -- hV : s + m = 4 * q * e * V
  have hVge : 4 * q * e ≤ s + m := Int.le_of_dvd (by omega) ⟨V, hV⟩
  have hV1 : 1 ≤ V := by
    have h2 : (4:ℤ) * q * e * 1 ≤ 4 * q * e * V := by
      rw [mul_one]
      rwa [hV] at hVge
    exact Int.le_of_mul_le_mul_left h2 h4qe
  -- V ≡ V₀ (mod A₀): cancel 4qe from 4qeA₀ ∣ 4qe(V−V₀)
  have hsm : s - (-m + 4 * q * e * V₀) = 4 * q * e * (V - V₀) := by
    linear_combination hV
  have hs2 : (4:ℤ) * q * e * A₀ ∣ 4 * q * e * (V - V₀) := by
    have h1 : (4:ℤ) * q * e * A₀ ∣ -(((-m + 4 * q * e * V₀) - s)) :=
      dvd_neg.mpr hs_dvd
    have heq : -(((-m + 4 * q * e * V₀) - s)) = 4 * q * e * (V - V₀) := by
      linear_combination hV
    rwa [heq] at h1
  have hVV₀ : A₀ ∣ (V - V₀) := by
    have h4 : (4:ℤ) * q * e * A₀ = (4 * q * e) * A₀ := by ring
    rw [h4] at hs2
    exact (mul_dvd_mul_iff_left h4qene).mp hs2
  -- A ∣ (qek·V₀ − u) from the solvability congruence
  have hAdvd : A ∣ (q * e * k * V₀ - u) := by
    have h1 : A ∣ (u - q * e * k * V₀) := (Int.modEq_iff_dvd).mp hV₀
    have h2 : A ∣ -(u - q * e * k * V₀) := dvd_neg.mpr h1
    rwa [neg_sub] at h2
  -- A ∣ qek·A₀ since A = A₀·g and g ∣ qek
  have hAqekA₀ : A ∣ q * e * k * A₀ := by
    obtain ⟨l, hl⟩ := hgq
    exact ⟨l, by rw [hAeq, hl]; ring⟩
  -- The c2 core: A ∣ (qek·V − u)
  have hcong : A ∣ (q * e * k * V - u) := by
    obtain ⟨j, hj⟩ := hVV₀
    have e1 : q * e * k * V - u = q * e * k * (A₀ * j) + (q * e * k * V₀ - u) := by
      rw [← hj]; ring
    rw [e1]
    apply dvd_add
    · have e2 : q * e * k * (A₀ * j) = (q * e * k * A₀) * j := by ring
      rw [e2]
      exact dvd_mul_of_dvd_left hAqekA₀ j
    · exact hAdvd
  -- sk+1 = 4(qeVk − u)
  have hsk : s * k + 1 = 4 * (q * e * V * k - u) := by
    have hsV : s = 4 * q * e * V - m := by linear_combination hV
    rw [hsV]; linear_combination -hk
  -- 4A ∣ sk+1
  have h4Advd : (4:ℤ) * A ∣ (s * k + 1) := by
    rw [hsk]
    have h1 : A ∣ (q * e * V * k - u) := by
      have e : q * e * V * k - u = q * e * k * V - u := by ring
      rw [e]; exact hcong
    exact mul_dvd_mul_left 4 h1
  obtain ⟨Q, hQ⟩ := h4Advd
  obtain ⟨P', hP'⟩ := hAS
  have hP'pos : 0 < P' := by
    have h1 : (0:ℤ) < A * P' := by rw [← hP']; exact hSpos
    rw [mul_comm] at h1
    exact pos_of_mul_pos h1 hA.le
  have hQpos : 0 < Q := by
    have h1 : (0:ℤ) < 4 * A * Q := by
      rw [← hQ]
      have h2 : 0 < s * k := mul_pos (by omega) hkpos
      omega
    rw [mul_comm] at h1
    exact pos_of_mul_pos h1 (by positivity)
  -- Casts to ℚ
  have hfQ : (f:ℚ) * S = r * q * e := by exact_mod_cast hf
  have hurQ : (u:ℚ) * r = A * S := by exact_mod_cast hur
  have hkQ : (m:ℚ) * k = 1 + 4 * u := by exact_mod_cast hk
  have hVQ : (s:ℚ) + m = 4 * q * e * V := by exact_mod_cast hV
  have hMQ : (Mp:ℚ) = 4 * S := by exact_mod_cast hM
  have hPQ : (S:ℚ) = A * P' := by exact_mod_cast hP'
  have hQQ : (4:ℚ) * A * Q = s * k + 1 := by exact_mod_cast hQ.symm
  -- The per-t identity
  intro t ht
  have eV : (s + m) / (4 * q * e) = V :=
    Int.ediv_eq_of_eq_mul_left h4qene (hV.trans (mul_comm _ _))
  have eP : S / A = P' := Int.ediv_eq_of_eq_mul_left hAne (hP'.trans (mul_comm _ _))
  have eQ : (s * k + 1) / (4 * A) = Q :=
    Int.ediv_eq_of_eq_mul_left h4Ane (hQ.trans (mul_comm _ _))
  -- Positivity of the four denominators / witnesses
  have hVpos : (0:ℤ) < V := by omega
  have hnpos : (0:ℤ) < Mp * t + s := by
    have h1 : (0:ℤ) ≤ Mp * t := mul_nonneg (le_of_lt hMpos) ht
    omega
  have hxpos : (0:ℤ) < S * t + q * e * V := by
    have h1 : (0:ℤ) ≤ S * t := mul_nonneg (le_of_lt hSpos) ht
    have h2 : (0:ℤ) < q * e * V := mul_pos (mul_pos hq he) hVpos
    omega
  have hBpos : (0:ℤ) < r * t + f * V := by
    have h1 : (0:ℤ) ≤ r * t := mul_nonneg (le_of_lt hr) ht
    have h2 : (0:ℤ) < f * V := mul_pos hfpos hVpos
    omega
  have hCpos : (0:ℤ) < P' * k * t + Q := by
    have h1 : (0:ℤ) ≤ P' * k * t := by
      have h2 : (0:ℤ) ≤ P' * k := mul_nonneg (le_of_lt hP'pos) (le_of_lt hkpos)
      exact mul_nonneg h2 ht
    omega
  have hn : (0:ℚ) < ((Mp * t + s : ℤ) : ℚ) := by exact_mod_cast hnpos
  have hx : (0:ℚ) < ((S * t + q * e * V : ℤ) : ℚ) := by exact_mod_cast hxpos
  have hB : (0:ℚ) < ((r * t + f * V : ℤ) : ℚ) := by exact_mod_cast hBpos
  have hC : (0:ℚ) < ((P' * k * t + Q : ℤ) : ℚ) := by exact_mod_cast hCpos
  have hAQ : (0:ℚ) < A := by exact_mod_cast hA
  have hSq : (0:ℚ) < S := by exact_mod_cast hSpos
  -- Rewrite the goal's edivs to the clean witnesses, then name the ℚ terms
  -- (set must precede any push_cast, which would destroy the patterns)
  rw [eV, eP, eQ]
  set nq : ℚ := ((Mp * t + s : ℤ) : ℚ) with hnqdef
  set xq : ℚ := ((S * t + q * e * V : ℤ) : ℚ) with hxqdef
  set Bq : ℚ := ((r * t + f * V : ℤ) : ℚ) with hBqdef
  set Cq : ℚ := ((P' * k * t + Q : ℤ) : ℚ) with hCqdef
  -- The relation chain
  have ha : (4:ℚ) * xq = nq + m := by
    rw [hxqdef, hnqdef]; push_cast
    linear_combination (-t) * hMQ - hVQ
  have hb : Bq * S = r * xq := by
    rw [hBqdef, hxqdef]; push_cast
    linear_combination (V : ℚ) * hfQ
  have hc : (4:ℚ) * A * Cq = k * nq + 1 := by
    rw [hCqdef, hnqdef]; push_cast
    linear_combination (-4 * k * t) * hPQ + hQQ + (-k * t) * hMQ
  have hmac : m * (A * Cq) = xq + u * nq := by
    linear_combination (m / 4) * hc + (nq / 4) * hkQ - (1 / 4) * ha
  have keyS : (A * xq - u * Bq) * S = 0 := by
    linear_combination (-u) * hb + (-xq) * hurQ
  have key : A * xq = u * Bq := by
    have h0 : A * xq - u * Bq = 0 := by
      rcases mul_eq_zero.mp keyS with h | h
      · exact h
      · exact absurd h (ne_of_gt hSq)
    exact sub_eq_zero.mp h0
  have hBCne : Bq * Cq ≠ 0 := mul_ne_zero hB.ne' hC.ne'
  have hNACXne : nq * A * Cq * xq ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hn.ne' hAQ.ne') hC.ne') hx.ne'
  have hNACne : nq * A * Cq ≠ 0 :=
    mul_ne_zero (mul_ne_zero hn.ne' hAQ.ne') hC.ne'
  have e1 : (1:ℚ) / (Bq * Cq) = (u * nq) / (nq * A * Cq * xq) := by
    rw [div_eq_div_iff hBCne hNACXne]
    have e : nq * A * Cq * xq = (u * nq) * (Bq * Cq) := by
      linear_combination (nq * Cq) * key
    rw [e, one_mul]
  have e2 : (1:ℚ) / (nq * A * Cq) = xq / (nq * A * Cq * xq) := by
    rw [div_eq_div_iff hNACne hNACXne]; ring
  have esum : (1:ℚ) / (nq * A * Cq) + 1 / (Bq * Cq) =
      (xq + u * nq) / (nq * A * Cq * xq) := by
    rw [e2, e1, ← add_div]
  have hACne : (A:ℚ) * Cq ≠ 0 := mul_ne_zero hAQ.ne' hC.ne'
  have em : (xq + u * nq) / (nq * A * Cq * xq) = m / (nq * xq) := by
    have hnx : nq * A * Cq * xq = (nq * xq) * (A * Cq) := by ac_rfl
    rw [hnx, ← hmac]
    exact mul_div_mul_right _ _ hACne
  have hfin : (m:ℚ) / (nq * xq) = 4 / nq - 1 / xq := by
    have ha' : (m:ℚ) = 4 * xq - nq := by linarith [ha]
    have h1 : nq ≠ 0 := hn.ne'
    have h2 : xq ≠ 0 := hx.ne'
    rw [ha']
    field_simp
  have hmain : (1:ℚ) / (nq * A * Cq) + 1 / (Bq * Cq) = m / (nq * xq) := by
    rw [esum, em]
  have key2 : (1:ℚ) / (nq * A * Cq) + 1 / (Bq * Cq) + 1 / xq = 4 / nq := by
    linarith [hmain, hfin]
  calc (4:ℚ) / nq = 1 / (nq * A * Cq) + 1 / (Bq * Cq) + 1 / xq := key2.symm
    _ = 1 / xq + 1 / (nq * A * Cq) + 1 / (Bq * Cq) := by ring

end ESSubfamilyExtended

namespace ESSubfamilyExtended

/-! ## R253: sharpened admission criterion (rule-9 review: SURVIVES, R266)

Review: ~/workspace/math-unsolved/review-r253-admission/review-transcript.txt
(Codex gpt-6-astra / ultra). Verdict: "The criterion survives, conditional on
R245 supplying the asserted integer setup. I found no counterexample."
The integrality condition (f ∣ A·qe, i.e. u = Aqe/f ∈ ℤ) is now an explicit
hypothesis; the R245 setup in this file supplies it via `hur`/`hf`. The
28,561-valuation-tuple exhaustive check is cited, not re-proved.
-/

/-- R253 per-prime five-case criterion, as a standalone Prop over the
    valuations α = v_p(A), β = v_p(qe), φ = v_p(f), κ = v_p(k). Case (e)
    ("no condition") contributes nothing. -/
def AdmCond (α β φ κ : ℕ) : Prop :=
  (β ≥ α → φ ≤ β) ∧ ¬(β < α ∧ φ > α) ∧
  (β < α → φ = α → κ = 0) ∧
  (β < α → β < φ → φ < α → κ ≤ α - φ)

/-- The local valuation inequality is equivalent to the five-case
    criterion (R253's (*), direction-audited; `omega` closes it). -/
theorem adm_val_criterion_iff (α β φ κ : ℕ) (hφ : φ ≤ α + β) :
    min α (β + κ) ≤ α + β - φ ↔ AdmCond α β φ κ := by
  unfold AdmCond
  omega

/-- Solvability of the admission congruence (qek)V ≡ u (mod A) is
    equivalent to gcd(A, qek) ∣ u (Bezout form of R253's "Solvability ⟺
    d ∣ u"). -/
theorem adm_congruence_solvable (A qe k u : ℕ) (hA : 0 < A) :
    (∃ V : ℤ, ((qe * k : ℕ) : ℤ) * V ≡ (u : ℤ) [ZMOD (A : ℤ)]) ↔
      ((Nat.gcd A (qe * k) : ℕ) : ℤ) ∣ (u : ℤ) := by
  have hcast : Int.gcd (A : ℤ) ((qe * k : ℕ) : ℤ) = ((Nat.gcd A (qe * k) : ℕ) : ℤ) := by
    rw [Int.gcd_natCast_natCast]
  constructor
  · rintro ⟨V, hV⟩
    rw [Int.modEq_iff_dvd] at hV
    have hdA : ((Nat.gcd A (qe * k) : ℕ) : ℤ) ∣ (A : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left A (qe * k)
    have hdq : ((Nat.gcd A (qe * k) : ℕ) : ℤ) ∣ ((qe * k : ℕ) : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_right A (qe * k)
    have h1 : ((Nat.gcd A (qe * k) : ℕ) : ℤ) ∣ ((u : ℤ) - ((qe * k : ℕ) : ℤ) * V) :=
      dvd_trans hdA hV
    have h2 : ((Nat.gcd A (qe * k) : ℕ) : ℤ) ∣ ((qe * k : ℕ) : ℤ) * V :=
      dvd_mul_of_dvd_left hdq V
    have h3 := dvd_add h1 h2
    have heq : ((u : ℤ) - ((qe * k : ℕ) : ℤ) * V) + ((qe * k : ℕ) : ℤ) * V = (u : ℤ) := by
      ring
    rwa [heq] at h3
  · rintro ⟨c, hc⟩
    have hbez : ((Nat.gcd A (qe * k) : ℕ) : ℤ)
        = (A : ℤ) * Int.gcdA (A : ℤ) ((qe * k : ℕ) : ℤ)
          + ((qe * k : ℕ) : ℤ) * Int.gcdB (A : ℤ) ((qe * k : ℕ) : ℤ) := by
      rw [← hcast, Int.gcd_eq_gcd_ab]
    refine ⟨Int.gcdB (A : ℤ) ((qe * k : ℕ) : ℤ) * c, ?_⟩
    rw [Int.modEq_iff_dvd]
    have key : (u : ℤ) - ((qe * k : ℕ) : ℤ) * (Int.gcdB (A : ℤ) ((qe * k : ℕ) : ℤ) * c)
        = (A : ℤ) * (Int.gcdA (A : ℤ) ((qe * k : ℕ) : ℤ) * c) := by
      rw [hc, hbez]; ring
    exact ⟨Int.gcdA (A : ℤ) ((qe * k : ℕ) : ℤ) * c, key⟩

/-- R253 sharpened admission criterion: with u = A·qe/f ∈ ℕ (the
    integrality the rule-9 review made a hypothesis), gcd(A, qe·k) ∣ u
    iff the five-case per-prime criterion holds at every prime. -/
theorem admission_criterion (A qe f k : ℕ)
    (hA : 0 < A) (hqe : 0 < qe) (hf : 0 < f) (hk : 0 < k)
    (hfint : f ∣ A * qe) :
    Nat.gcd A (qe * k) ∣ (A * qe / f) ↔
      ∀ p : ℕ, p.Prime →
        AdmCond (A.factorization p) (qe.factorization p)
          (f.factorization p) (k.factorization p) := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hqene : qe ≠ 0 := ne_of_gt hqe
  have hkne : k ≠ 0 := ne_of_gt hk
  have hfne : f ≠ 0 := ne_of_gt hf
  have hqkne : qe * k ≠ 0 := mul_ne_zero hqene hkne
  have hAqe : A * qe ≠ 0 := mul_ne_zero hAne hqene
  have hgpos : 0 < Nat.gcd A (qe * k) :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left A (qe * k)) hA
  have hune : A * qe / f ≠ 0 := by
    have h1 : A * qe / f * f = A * qe := Nat.div_mul_cancel hfint
    rintro h0
    rw [h0, zero_mul] at h1
    have h2 : 0 < A * qe := by positivity
    omega
  have hφ : ∀ p : ℕ, p.Prime →
      f.factorization p ≤ A.factorization p + qe.factorization p := by
    intro p _
    have hle0 := (Nat.factorization_le_iff_dvd hfne hAqe).mpr hfint
    have hlep := (Finsupp.le_def.mp hle0) p
    have hmul := Nat.factorization_mul hAne hqene
    have h2p := DFunLike.congr_fun hmul p
    rw [Finsupp.add_apply] at h2p
    omega
  have hfac : ∀ p : ℕ, p.Prime →
      (Nat.gcd A (qe * k)).factorization p
        = min (A.factorization p) (qe.factorization p + k.factorization p) ∧
      (A * qe / f).factorization p
        = A.factorization p + qe.factorization p - f.factorization p := by
    intro p hp
    have h1 : (Nat.gcd A (qe * k)).factorization p
        = min (A.factorization p) ((qe * k).factorization p) := by
      have h := DFunLike.congr_fun (Nat.factorization_gcd hAne hqkne) p
      rw [Finsupp.inf_apply] at h
      exact h
    have hmul := Nat.factorization_mul hqene hkne
    have h2p := DFunLike.congr_fun hmul p
    rw [Finsupp.add_apply] at h2p
    have hdiv := Nat.factorization_div hfint
    have hmul2 := Nat.factorization_mul hAne hqene
    have h3p := DFunLike.congr_fun hdiv p
    rw [Finsupp.tsub_apply] at h3p
    have h4p := DFunLike.congr_fun hmul2 p
    rw [Finsupp.add_apply] at h4p
    constructor <;> omega
  rw [← Nat.factorization_le_iff_dvd hgpos.ne' hune]
  constructor
  · intro h p hp
    have hle := (Finsupp.le_def.mp h) p
    obtain ⟨h1, h3⟩ := hfac p hp
    rw [h1, h3] at hle
    exact (adm_val_criterion_iff _ _ _ _ (hφ p hp)).mp hle
  · intro h
    rw [Finsupp.le_def]
    intro p
    by_cases hpp : p.Prime
    · obtain ⟨h1, h3⟩ := hfac p hpp
      rw [h1, h3]
      exact (adm_val_criterion_iff _ _ _ _ (hφ p hpp)).mpr (h p hpp)
    · have z1 : (Nat.gcd A (qe * k)).factorization p = 0 :=
        (Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hpp)
      have z2 : (A * qe / f).factorization p = 0 :=
        (Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hpp)
      omega

/-! ## R261: A₀-constancy (rule-9 review: SURVIVES with stronger formula, R266)

Review: ~/workspace/math-unsolved/review-r261-a0constancy/review-transcript.txt
(Codex gpt-6-astra / ultra). Verdict: "The A₀-constancy theorem survives.
The appended corollary does not: both '⟺' statements are false as written."
The valuation argument proves the stronger explicit formula
A₀(m) = A/gcd(A, qe), formalized here. The unconditional ⟺ corollary is
NOT formalized as stated; its corrected restatement (reviewer's repair:
equivalences hold when at least one parent set is nonempty) is
`split_layered_restated` below.
-/

/-- R261 (S1): u = A·qe/f as an exact equation, avoiding division. -/
theorem u_eq_Aqe_div_f (A qe f u : ℕ) (hf : 0 < f) (hu_eq : u * f = A * qe) :
    u = A * qe / f := by
  have h1 : u * f / f = u := Nat.mul_div_cancel u hf
  rw [← h1, hu_eq]

/-- R261 (S3): an excess prime (v_p(f) < v_p(A)) divides u = A·qe/f. -/
theorem excess_prime_dvd_u (A qe f : ℕ) (hA : 0 < A) (hqe : 0 < qe) (hf : 0 < f)
    (hfint : f ∣ A * qe) (p : ℕ) (hp : p.Prime)
    (hlt : f.factorization p < A.factorization p) :
    p ∣ A * qe / f := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hqene : qe ≠ 0 := ne_of_gt hqe
  have hfne : f ≠ 0 := ne_of_gt hf
  obtain ⟨c, hc⟩ := hfint
  have hcne : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    have h2 : 0 < A * qe := by positivity
    omega
  have hdiv : A * qe / f = c := by
    rw [hc]; exact Nat.mul_div_cancel_left c hf
  rw [hdiv]
  have h1 : (f * c).factorization = (A * qe).factorization := by rw [← hc]
  have h1p := DFunLike.congr_fun h1 p
  have hmul1 := Nat.factorization_mul hfne hcne
  have hmul2 := Nat.factorization_mul hAne hqene
  have h2p := DFunLike.congr_fun hmul1 p
  have h3p := DFunLike.congr_fun hmul2 p
  rw [Finsupp.add_apply] at h2p h3p
  rw [h2p, h3p] at h1p
  have hpos : 1 ≤ c.factorization p := by omega
  exact dvd_trans (dvd_pow_self p (by omega)) (Nat.ordProj_dvd c p)

/-- R261 pinning lemma (cases (d),(e)): at an excess prime with
    v_p(f) < v_p(A), p ∣ u, so p ∤ D₀ = 1+4u, so v_p(k) = 0 for m·k = D₀. -/
theorem pinning_lemma (A qe f : ℕ) (hA : 0 < A) (hqe : 0 < qe) (hf : 0 < f)
    (hfint : f ∣ A * qe) (p : ℕ) (hp : p.Prime)
    (hex : qe.factorization p < A.factorization p)
    (hlt : f.factorization p < A.factorization p)
    (m : ℕ) (hm : m ∣ 1 + 4 * (A * qe / f))
    (k : ℕ) (hk : m * k = 1 + 4 * (A * qe / f)) :
    k.factorization p = 0 := by
  have hpu : p ∣ A * qe / f :=
    excess_prime_dvd_u A qe f hA hqe hf hfint p hp hlt
  have hnp : ¬ p ∣ 1 + 4 * (A * qe / f) := by
    intro hdiv
    have h4u : p ∣ 4 * (A * qe / f) := dvd_mul_of_dvd_right hpu 4
    have h1 : (p : ℤ) ∣ ((1 + 4 * (A * qe / f) : ℕ) : ℤ) := by exact_mod_cast hdiv
    have h2 : (p : ℤ) ∣ ((4 * (A * qe / f) : ℕ) : ℤ) := by exact_mod_cast h4u
    have h3 : (p : ℤ) ∣ ((1 + 4 * (A * qe / f) : ℕ) : ℤ) - ((4 * (A * qe / f) : ℕ) : ℤ) :=
      dvd_sub h1 h2
    have heq : ((1 + 4 * (A * qe / f) : ℕ) : ℤ) - ((4 * (A * qe / f) : ℕ) : ℤ) = 1 := by
      push_cast; ring
    have h4 : (p : ℤ) ∣ (1 : ℤ) := by rwa [heq] at h3
    have h5 : p ∣ 1 := Int.natCast_dvd_natCast.mp h4
    have h6 : p ≤ 1 := Nat.le_of_dvd (by norm_num) h5
    have h7 : 2 ≤ p := hp.two_le
    omega
  by_contra hne
  have hpk : p ∣ k := by
    have h1k : 1 ≤ k.factorization p := Nat.one_le_iff_ne_zero.mpr hne
    exact dvd_trans (dvd_pow_self p (by omega)) (Nat.ordProj_dvd k p)
  have hpmk : p ∣ m * k := dvd_mul_of_dvd_right hpk m
  rw [hk] at hpmk
  exact hnp hpmk

/-- R261: the R253 criterion pins κ_p = 0 at every excess prime for an
    admitted complementary divisor (case (c) directly; cases (d),(e) via
    the pinning lemma; case (b) excludes φ_p > α_p). -/
theorem admission_pinning (A qe f k : ℕ) (hA : 0 < A) (hqe : 0 < qe) (hf : 0 < f)
    (hfint : f ∣ A * qe)
    (hadm : ∀ p : ℕ, p.Prime →
      AdmCond (A.factorization p) (qe.factorization p)
        (f.factorization p) (k.factorization p))
    (m : ℕ) (hk : m * k = 1 + 4 * (A * qe / f)) :
    ∀ p : ℕ, p.Prime → qe.factorization p < A.factorization p →
      k.factorization p = 0 := by
  intro p hp hex
  obtain ⟨_, h2, h3, _⟩ := hadm p hp
  by_cases hφ : f.factorization p = A.factorization p
  · exact h3 hex hφ
  · have hlt : f.factorization p < A.factorization p := by
      have hle : f.factorization p ≤ A.factorization p := by
        by_contra hcon
        push_neg at hcon
        exact h2 ⟨hex, hcon⟩
      omega
    exact pinning_lemma A qe f hA hqe hf hfint p hp hex hlt m ⟨k, hk.symm⟩ k hk

/-- R261 stronger formula (per the rule-9 review): an admitted k gives
    A₀ = A/gcd(A, qe·k) = A/gcd(A, qe), a shape-level constant. -/
theorem a0_constancy_formula (A qe k : ℕ) (hA : 0 < A) (hqe : 0 < qe) (hk : 0 < k)
    (hpin : ∀ p : ℕ, p.Prime →
      qe.factorization p < A.factorization p → k.factorization p = 0) :
    A / Nat.gcd A (qe * k) = A / Nat.gcd A qe := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hqene : qe ≠ 0 := ne_of_gt hqe
  have hkne : k ≠ 0 := ne_of_gt hk
  have hg1 : 0 < Nat.gcd A (qe * k) :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left A (qe * k)) hA
  have hg2 : 0 < Nat.gcd A qe :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left A qe) hA
  have hd1 : A / Nat.gcd A (qe * k) ≠ 0 := by
    have h := Nat.div_pos (Nat.le_of_dvd hA (Nat.gcd_dvd_left A (qe * k))) hg1
    omega
  have hd2 : A / Nat.gcd A qe ≠ 0 := by
    have h := Nat.div_pos (Nat.le_of_dvd hA (Nat.gcd_dvd_left A qe)) hg2
    omega
  apply Nat.eq_of_factorization_eq hd1 hd2
  intro p
  have e1 := Nat.factorization_div (Nat.gcd_dvd_left A (qe * k))
  have e2 := Nat.factorization_div (Nat.gcd_dvd_left A qe)
  have p1 := DFunLike.congr_fun e1 p
  have p2 := DFunLike.congr_fun e2 p
  rw [Finsupp.tsub_apply] at p1 p2
  by_cases hpp : p.Prime
  · have g1 : (Nat.gcd A (qe * k)).factorization p
        = min (A.factorization p) ((qe * k).factorization p) := by
      have h := DFunLike.congr_fun
        (Nat.factorization_gcd hAne (mul_ne_zero hqene hkne)) p
      rw [Finsupp.inf_apply] at h
      exact h
    have g2 : (Nat.gcd A qe).factorization p
        = min (A.factorization p) (qe.factorization p) := by
      have h := DFunLike.congr_fun (Nat.factorization_gcd hAne hqene) p
      rw [Finsupp.inf_apply] at h
      exact h
    have m1 := Nat.factorization_mul hqene hkne
    have m1p := DFunLike.congr_fun m1 p
    rw [Finsupp.add_apply] at m1p
    by_cases hex : qe.factorization p < A.factorization p
    · have hkz := hpin p hpp hex
      rw [p1, p2, g1, g2, m1p, hkz]
      omega
    · push_neg at hex
      rw [p1, p2, g1, g2, m1p]
      omega
  · have z1 : (Nat.gcd A (qe * k)).factorization p = 0 :=
      (Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hpp)
    have z2 : (Nat.gcd A qe).factorization p = 0 :=
      (Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hpp)
    have zA : A.factorization p = 0 :=
      (Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hpp)
    rw [p1, p2]
    omega

/-- R261 A₀-constancy: two admitted complementary divisors give the same A₀. -/
theorem a0_constancy (A qe k₁ k₂ : ℕ) (hA : 0 < A) (hqe : 0 < qe)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hpin₁ : ∀ p : ℕ, p.Prime →
      qe.factorization p < A.factorization p → k₁.factorization p = 0)
    (hpin₂ : ∀ p : ℕ, p.Prime →
      qe.factorization p < A.factorization p → k₂.factorization p = 0) :
    A / Nat.gcd A (qe * k₁) = A / Nat.gcd A (qe * k₂) := by
  rw [a0_constancy_formula A qe k₁ hA hqe hk₁ hpin₁,
    a0_constancy_formula A qe k₂ hA hqe hk₂ hpin₂]

/-- R261 A₀-constancy, packaged for admitted m₁, m₂ (pinning derived from
    the R253 criterion via `admission_pinning`). -/
theorem a0_constancy_admitted (A qe f k₁ k₂ m₁ m₂ : ℕ)
    (hA : 0 < A) (hqe : 0 < qe) (hf : 0 < f)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hfint : f ∣ A * qe)
    (hadm₁ : ∀ p : ℕ, p.Prime →
      AdmCond (A.factorization p) (qe.factorization p)
        (f.factorization p) (k₁.factorization p))
    (hadm₂ : ∀ p : ℕ, p.Prime →
      AdmCond (A.factorization p) (qe.factorization p)
        (f.factorization p) (k₂.factorization p))
    (hkD₁ : m₁ * k₁ = 1 + 4 * (A * qe / f))
    (hkD₂ : m₂ * k₂ = 1 + 4 * (A * qe / f)) :
    A / Nat.gcd A (qe * k₁) = A / Nat.gcd A (qe * k₂) :=
  a0_constancy A qe k₁ k₂ hA hqe hk₁ hk₂
    (admission_pinning A qe f k₁ hA hqe hf hfint hadm₁ m₁ hkD₁)
    (admission_pinning A qe f k₂ hA hqe hf hfint hadm₂ m₂ hkD₂)

/-- R261 M-constancy: M(m) = 4·qe·A₀(m) is shape-level constant. -/
theorem M_const (A qe k₁ k₂ : ℕ) (hA : 0 < A) (hqe : 0 < qe)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hpin₁ : ∀ p : ℕ, p.Prime →
      qe.factorization p < A.factorization p → k₁.factorization p = 0)
    (hpin₂ : ∀ p : ℕ, p.Prime →
      qe.factorization p < A.factorization p → k₂.factorization p = 0) :
    4 * qe * (A / Nat.gcd A (qe * k₁)) = 4 * qe * (A / Nat.gcd A (qe * k₂)) := by
  rw [a0_constancy A qe k₁ k₂ hA hqe hk₁ hk₂ hpin₁ hpin₂]

/-! ## R261 corrected corollary restatement (rule-9 reviewer's repair, R266)

The unconditional ⟺ as stated in R261 is FALSE (reviewer counterexample:
q=29, A=10, r=510510 — three admitted values with EMPTY parent sets, which
are both identical and disjoint). The reviewer's prescribed repair:
"retain R256's valid domain and replace both ⟺ symbols by ⇒; alternatively,
within that domain, the equivalences hold if at least one of the two parent
sets is nonempty." Formalized here is the alternative: with parent-set
determination (R256's valid domain) as a hypothesis and at least one parent
set nonempty, both ⟺ statements hold. The determination itself is NOT
proved here (R256's review is MIXED — see ROUND266_DOSSIER.md).
-/

/-- R261 split/layered dichotomy, corrected restatement: parent sets
    determined by the residue class mod g (R256's valid domain, cited);
    with at least one parent set nonempty, identical ⟺ equal residues and
    disjoint ⟺ distinct residues. -/
theorem split_layered_restated (Parents : Finset ℕ) (g res₁ res₂ : ℕ)
    (P₁ P₂ : Finset ℕ)
    (hdet₁ : P₁ = Parents.filter (fun s' => s' % g = res₁ % g))
    (hdet₂ : P₂ = Parents.filter (fun s' => s' % g = res₂ % g))
    (hne : P₁.Nonempty) :
    (P₁ = P₂ ↔ res₁ % g = res₂ % g) ∧
      (Disjoint P₁ P₂ ↔ res₁ % g ≠ res₂ % g) := by
  have heq : res₁ % g = res₂ % g → P₁ = P₂ := by
    intro h
    rw [hdet₁, hdet₂, h]
  refine ⟨⟨?_, heq⟩, ⟨?_, ?_⟩⟩
  · intro hP
    obtain ⟨s', hs'⟩ := hne
    have hs1 : s' ∈ Parents.filter (fun s' => s' % g = res₁ % g) := by
      rw [← hdet₁]; exact hs'
    have hs2 : s' ∈ Parents.filter (fun s' => s' % g = res₂ % g) := by
      rw [← hdet₂, ← hP]; exact hs'
    have h1 : s' % g = res₁ % g := (Finset.mem_filter.mp hs1).2
    have h2 : s' % g = res₂ % g := (Finset.mem_filter.mp hs2).2
    omega
  · intro hD hcon
    have hD2 : Disjoint P₂ P₂ := heq hcon ▸ hD
    have hne2 : P₂.Nonempty := heq hcon ▸ hne
    obtain ⟨x, hx⟩ := hne2
    exact (Finset.disjoint_left.mp hD2 hx) hx
  · intro hne'
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hx1' : x ∈ Parents.filter (fun s' => s' % g = res₁ % g) := by
      rw [← hdet₁]; exact hx1
    have hx2' : x ∈ Parents.filter (fun s' => s' % g = res₂ % g) := by
      rw [← hdet₂]; exact hx2
    have h1 : x % g = res₁ % g := (Finset.mem_filter.mp hx1').2
    have h2 : x % g = res₂ % g := (Finset.mem_filter.mp hx2').2
    exact hne' (by omega)

end ESSubfamilyExtended

namespace ESSubfamilyExtended

/-- R265 repaired split/layered dichotomy — fold of the rule-9-reviewed
    [PROVED*] theorem (see ROUND265_DOSSIER.md "Formalizable restatement").
    Rule-9 review (Bunny, Q-10, 2026-10-10): "SURVIVES under cited
    assumptions", 9/9 checks, "no Lean claim" (#agents ts
    1791669332.842259, 16:05 PDT confirmation "conditional SURVIVES").
    (a) SPLIT and (b) LAYERED are forced UNCONDITIONALLY (no nonemptiness
    hypothesis — this is the repair over `split_layered_restated`);
    (c) both upgrade to ⟺ under the sharp hypothesis that at least one
    parent set is nonempty. The determination is R256's, cited as a
    hypothesis, not proved here. -/
theorem split_layered_repaired (Parents : Finset ℕ) (g res₁ res₂ : ℕ)
    (P₁ P₂ : Finset ℕ)
    (hdet₁ : P₁ = Parents.filter (fun s' => s' % g = res₁ % g))
    (hdet₂ : P₂ = Parents.filter (fun s' => s' % g = res₂ % g)) :
    (res₁ % g ≠ res₂ % g → Disjoint P₁ P₂) ∧
    (res₁ % g = res₂ % g → P₁ = P₂) ∧
    ((P₁ ∪ P₂).Nonempty →
      (Disjoint P₁ P₂ ↔ res₁ % g ≠ res₂ % g) ∧
      (P₁ = P₂ ↔ res₁ % g = res₂ % g)) := by
  have heq : res₁ % g = res₂ % g → P₁ = P₂ := by
    intro h
    rw [hdet₁, hdet₂, h]
  have hdis : res₁ % g ≠ res₂ % g → Disjoint P₁ P₂ := by
    intro hne'
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hx1' : x ∈ Parents.filter (fun s' => s' % g = res₁ % g) := by
      rw [← hdet₁]; exact hx1
    have hx2' : x ∈ Parents.filter (fun s' => s' % g = res₂ % g) := by
      rw [← hdet₂]; exact hx2
    have h1 : x % g = res₁ % g := (Finset.mem_filter.mp hx1').2
    have h2 : x % g = res₂ % g := (Finset.mem_filter.mp hx2').2
    exact hne' (by omega)
  refine ⟨hdis, heq, ?_⟩
  intro hU
  obtain ⟨x, hx⟩ := hU
  rcases Finset.mem_union.mp hx with hx1 | hx2
  · obtain ⟨hP, hD⟩ :=
      split_layered_restated Parents g res₁ res₂ P₁ P₂ hdet₁ hdet₂ ⟨x, hx1⟩
    exact ⟨hD, hP⟩
  · obtain ⟨hP, hD⟩ :=
      split_layered_restated Parents g res₂ res₁ P₂ P₁ hdet₂ hdet₁ ⟨x, hx2⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro hdp
      exact Ne.symm (hD.mp (disjoint_comm.mp hdp))
    · intro hne'
      exact disjoint_comm.mpr (hD.mpr (Ne.symm hne'))
    · intro hpp
      exact (hP.mp hpp.symm).symm
    · intro hrr
      exact (hP.mpr hrr.symm).symm

end ESSubfamilyExtended
