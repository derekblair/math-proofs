import Mathlib
import Mathproofs.ESX0S1S3

/-!
# General Descent Transfer (R112; R108 proof)

Source: `~/workspace/math-unsolved/ROUND108_DOSSIER.md` §§1–3 (Round 108, [PROVED*]);
`~/workspace/math-unsolved/ROUND112_DOSSIER.md` §B.1 (Round 112, q-generic audit [PROVED*]).

Setup: M₀ = 2042040, XSTEP₀ = M₀/4 = 510510, q prime with q ∤ M₀, M′ = q·M₀,
XSTEP′ = q·XSTEP₀. A branch-2 Erdős–Straus identity (A, r₁, m, s′) at M′ with
s′ ≢ 0 (mod q).

Since A, r₁ | XSTEP′ = q·XSTEP₀ with q ∤ XSTEP₀: v_q(A), v_q(r₁) ∈ {0,1}.

The transfer descends the key relation `m | P₂` — in cross-multiplied form
`m * (A * r₁) ∣ XSTEP * (A + r₁)` (P₂ = XSTEP/A + XSTEP/r₁ = XSTEP·(A+r₁)/(A·r₁),
so `m | P₂` is `∃ k, XSTEP·(A+r₁) = k·m·(A·r₁)`) — from M′ to M₀:

- §2(a): `euclid_XSTEP` — A, r₁ | q·XSTEP₀ with q ∤ A (the (0,0) case) gives
  A | XSTEP₀.
- §2(b): `sformula_y_free` — the s-formula s′ ≡ 4A′B′y (mod q) with s′ ≢ 0
  (mod q) forces q ∤ y. (Explicit framework input: the congruence.)
- §2(b): `mu_valuation_of_sformula` — the S1S3-collapsed divisibility
  m·d₀ | y·(A′+B′) (the target of the machine-checked `ESX0S1S3.lemma_S1S3_ii`)
  with m = q^μ·m₀ and q ∤ y gives q^μ | A′+B′.
- §2(b): `mu_valuation_of_S3` — chains the machine-checked
  `ESX0S1S3.lemma_S1S3_ii` into `mu_valuation_of_sformula`: the (S3)
  q-integrality at M′ yields the s-formula input q^μ | A′+B′.
- §2(b) assembled: `transfer_key_00` — the (0,0) key lemma: with
  hμ : q^μ | A′+B′ (the s-formula input; trivial for μ = 0 via `one_dvd`) and
  the at-M′ key relation, the at-M₀ key relation holds. The paper's two
  subcases are unified: μ = 0 via Euclid on the q-free part; μ ≥ 1 by
  re-attaching q^μ through hμ.
- §3(a): `transfer_qcancel` — the (1,1) exact q-cancellation: with
  A = q·A₀, r₁ = q·r₀, XSTEP′ = q·XSTEP₀, the key relation at M′ on (A, r₁) is
  equivalent to the key relation at M₀ on (A₀, r₀) (P₂′ = P₂⁰₀ exactly).

Explicitly NOT formalized here (remain [PROVED*] on paper): the at-M′ key
relation itself (framework input from the branch-2 s-formula), the (c)–(g)
identity algebra (p″/qq₀/x₀‴ descent), and the R74 sweep-contradiction source.
-/

namespace ESDescentTransfer

/-- R108 §2(a): with q ∤ A (the (0,0) case), `A ∣ q·XSTEP₀` descends to `A ∣ XSTEP₀`. -/
theorem euclid_XSTEP {q A X : ℕ} (hq : q.Prime) (hA0 : ¬ q ∣ A)
    (hdvd : A ∣ q * X) : A ∣ X :=
  (hq.coprime_iff_not_dvd.mpr hA0).symm.dvd_of_dvd_mul_left hdvd

/-- R108 §2(b): the s-formula `s′ ≡ 4A′B′y (mod q)` with `s′ ≢ 0 (mod q)`
    forces `q ∤ y`. -/
theorem sformula_y_free {q s' A' B' y : ℕ}
    (hne : s' % q ≠ 0)
    (hformula : s' ≡ 4 * A' * B' * y [MOD q]) :
    ¬ q ∣ y := by
  intro hqy
  obtain ⟨k, hk⟩ := hqy
  have h1 : q ∣ 4 * A' * B' * y := ⟨(4 * A' * B') * k, by rw [hk]; ring⟩
  have h2 : (4 * A' * B' * y) ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr h1
  have h3 : s' ≡ 0 [MOD q] := hformula.trans h2
  have h4 : q ∣ s' := Nat.modEq_zero_iff_dvd.mp h3
  exact hne (Nat.dvd_iff_mod_eq_zero.mp h4)

/-- R108 §2(b): from the S1S3-collapsed divisibility `m·d₀ ∣ y·(A′+B′)` with
    `m = q^μ·m₀` and `q ∤ y`, the s-formula consequence `q^μ ∣ A′+B′`. -/
theorem mu_valuation_of_sformula {q μ m m₀ d₀ A' B' y : ℕ}
    (hq : q.Prime) (hm : m = q ^ μ * m₀)
    (hy : ¬ q ∣ y)
    (hcoll : m * d₀ ∣ y * (A' + B')) :
    q ^ μ ∣ A' + B' := by
  have hcop : Nat.Coprime (q ^ μ) y :=
    (hq.coprime_iff_not_dvd.mpr hy).pow_left μ
  rw [hm] at hcoll
  have hqμ : q ^ μ ∣ y * (A' + B') := by
    have h : q ^ μ ∣ (q ^ μ * m₀) * d₀ := ⟨m₀ * d₀, by ring⟩
    exact h.trans hcoll
  exact hcop.dvd_of_dvd_mul_left hqμ

/-- R108 §2(b) via the machine-checked S1S3: the (S3) q-integrality at M′,
    `m·A·r₁ ∣ x₀·(A+r₁)`, collapses (by `ESX0S1S3.lemma_S1S3_ii`) to
    `m·d₀ ∣ y·(A′+B′)`, hence the s-formula input `q^μ ∣ A′+B′`. -/
theorem mu_valuation_of_S3 {m A r₁ x₀ q μ m₀ d₀ A' B' y : ℕ}
    (hq : q.Prime) (hm : m = q ^ μ * m₀)
    (hd₀ : 0 < d₀) (hAB : 0 < A' * B')
    (hA : A = d₀ * A') (hr : r₁ = d₀ * B') (hx : x₀ = A' * B' * y)
    (hy : ¬ q ∣ y)
    (hS3 : m * A * r₁ ∣ x₀ * (A + r₁)) :
    q ^ μ ∣ A' + B' := by
  have hcoll : m * d₀ ∣ y * (A' + B') :=
    (ESX0S1S3.lemma_S1S3_ii hd₀ hAB hA hr hx).mp hS3
  exact mu_valuation_of_sformula hq hm hy hcoll

/-- R108 §2(b) assembled — the (0,0) key lemma: the at-M′ relation
    `m·(A·r₁) ∣ XSTEP′·(A+r₁)` descends to the at-M₀ relation
    `m·(A·r₁) ∣ XSTEP₀·(A+r₁)`.

    The s-formula input `hμ : q^μ ∣ A′+B′` unifies the paper's two subcases:
    μ = 0 (trivial input; Euclid on the q-free part) and μ ≥ 1 (re-attach q^μ
    through hμ). -/
theorem transfer_key_00 {q μ m m₀ d₀ A' B' A r₁ XSTEP' XSTEP₀ : ℕ}
    (hq : q.Prime)
    (hA : A = d₀ * A') (hr : r₁ = d₀ * B')
    (hm : m = q ^ μ * m₀)
    (hA0 : ¬ q ∣ A) (hr0 : ¬ q ∣ r₁) (hm0 : ¬ q ∣ m₀)
    (hX : XSTEP' = q * XSTEP₀)
    (hμ : q ^ μ ∣ A' + B')
    (hkey : m * (A * r₁) ∣ XSTEP' * (A + r₁)) :
    m * (A * r₁) ∣ XSTEP₀ * (A + r₁) := by
  have cA : Nat.Coprime q A := hq.coprime_iff_not_dvd.mpr hA0
  have cr : Nat.Coprime q r₁ := hq.coprime_iff_not_dvd.mpr hr0
  have cm : Nat.Coprime q m₀ := hq.coprime_iff_not_dvd.mpr hm0
  -- the q-free part is coprime to q
  have cN : Nat.Coprime (m₀ * (A * r₁)) q :=
    (cm.mul_right (cA.mul_right cr)).symm
  have cNq : Nat.Coprime (q ^ μ) (m₀ * (A * r₁)) :=
    (cm.pow_left μ).mul_right ((cA.pow_left μ).mul_right (cr.pow_left μ))
  -- Step 1: the q-free part descends via Euclid
  have h1 : m₀ * (A * r₁) ∣ q * (XSTEP₀ * (A + r₁)) := by
    rw [hm, hX] at hkey
    have e1 : q ^ μ * m₀ * (A * r₁) = q ^ μ * (m₀ * (A * r₁)) := by ring
    have e2 : q * XSTEP₀ * (A + r₁) = q * (XSTEP₀ * (A + r₁)) := by ring
    rw [e1, e2] at hkey
    exact Nat.dvd_trans (⟨q ^ μ, by ring⟩ : m₀ * (A * r₁) ∣ q ^ μ * (m₀ * (A * r₁))) hkey
  have h2 : m₀ * (A * r₁) ∣ XSTEP₀ * (A + r₁) := cN.dvd_of_dvd_mul_left h1
  -- Step 2: re-attach q^μ through the s-formula input
  have hAr : A + r₁ = d₀ * (A' + B') := by rw [hA, hr]; ring
  have hqμdvd : q ^ μ ∣ XSTEP₀ * (A + r₁) := by
    rw [hAr]
    obtain ⟨t, ht⟩ := hμ
    exact ⟨XSTEP₀ * (d₀ * t), by rw [ht]; ring⟩
  obtain ⟨k, hk⟩ := h2
  have hqk : q ^ μ ∣ k := by
    have hqk2 : q ^ μ ∣ (m₀ * (A * r₁)) * k := by
      rw [← hk]; exact hqμdvd
    exact cNq.dvd_of_dvd_mul_left hqk2
  obtain ⟨k', hk'⟩ := hqk
  rw [hm]
  exact ⟨k', by rw [hk, hk']; ring⟩

/-- R108 §3(a) — the (1,1) exact q-cancellation: with `A = q·A₀`, `r₁ = q·r₀`,
    `XSTEP′ = q·XSTEP₀`, the key relation at M′ on (A, r₁) is equivalent to the
    key relation at M₀ on (A₀, r₀) (P₂′ = P₂⁰₀ exactly; the q's cancel). -/
theorem transfer_qcancel {q m A₀ r₀ A r₁ XSTEP' XSTEP₀ : ℕ}
    (hq : 0 < q)
    (hA : A = q * A₀) (hr : r₁ = q * r₀) (hX : XSTEP' = q * XSTEP₀) :
    (m * (A₀ * r₀) ∣ XSTEP₀ * (A₀ + r₀)) ↔
    (m * (A * r₁) ∣ XSTEP' * (A + r₁)) := by
  have e1 : A * r₁ = q * q * (A₀ * r₀) := by rw [hA, hr]; ring
  have e2 : XSTEP' * (A + r₁) = q * q * (XSTEP₀ * (A₀ + r₀)) := by
    rw [hA, hr, hX]; ring
  rw [e1, e2]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩
  · rintro ⟨k, hk⟩
    have hpos : 0 < q * q := Nat.mul_pos hq hq
    have hk2 : (q * q) * (XSTEP₀ * (A₀ + r₀)) = (q * q) * ((m * (A₀ * r₀)) * k) := by
      rw [hk]; ring
    have hcancel := Nat.mul_left_cancel hpos hk2
    exact ⟨k, hcancel⟩

end ESDescentTransfer
