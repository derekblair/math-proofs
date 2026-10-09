import Mathlib
import Mathproofs.ESDescentTransfer

/-!
# Branch-1 q-adic type theorem (R116)

Source: `~/workspace/math-unsolved/ROUND116_DOSSIER.md` §A (Round 116, [PROVED*]).

Setup: M₀ = 2042040, XSTEP₀ = M₀/4 = 510510, q an odd prime with q ∤ M₀
(in the paper q ∈ {19, 23}; the proof is fully q-generic), M′ = q·M₀,
XSTEP′ = q·XSTEP₀. A branch-1 Erdős–Straus identity (A, r, m, s′) at M′ on a
refined target s′ (q ∤ s′), with A | XSTEP′, r | XSTEP′², so that with
A = q^α·A₀, r = q^ρ·r₀ (q ∤ A₀, r₀) we have α ∈ {0,1}, ρ ∈ {0,1,2}.

**Theorem** (`qadic_type_restriction`): (α, ρ) ∈ {(0,0), (1,0), (1,1)},
i.e. v_q(r) ≤ v_q(A). Three kills:

- `kill_02`: type (0,2) dies via the q | p valuation squeeze —
  α = 0 gives A′ = XSTEP′/A ≡ 0 (mod q), the s-congruence forces q | p,
  hence q | P′; but P′ = q·k₀ + 4·t₀ with q ∤ 4·t₀ (strict minimum), a
  contradiction.
- `kill_12`: type (1,2) dies via the q-adic expansion of R67's original
  condition (iii): with A = q·A₀, r = q²·r₀, XSTEP′ = q·X₀ and
  q | (s′+m) (Lemma M23′), the numerator r·x₀ + A·s′·XSTEP′ equals
  q²·w with q | w, while the denominator is q³·v₀; integrality of QQ
  (hQQ) forces q | w, and then q | A₀·s′·X₀, contradicting q ∤ A₀, s′, X₀.
- `descent_01`: type (0,1) descends — with A = A₀, r = q·r₀, the exact
  q-cancellation P′ = q·P₀ plus m | P₀ (coprime to q) and the congruence
  descent give a full branch-1 bundle at M₀ on s₀, contradicting the
  R74 complete-sweep input (hR74).

Also formalized: `qpow_le_of_dvd_pow` (the α ≤ 1 / ρ ≤ 2 valuation bounds
from Euclid's lemma) and `m23_qfree` (Lemma M23′'s key content:
s′ + m ≡ 0 (mod q) with q ∤ s′ gives q ∤ m).

Explicitly NOT formalized here (remain [PROVED*] on paper / [COMPUTED]):
the R74 sweep-contradiction source (explicit hypothesis hR74), R67 (iii)'s
QQ-integrality (explicit hypothesis hQQ), and the full Lemma M23′
(the q | (s′+m) and q ∤ m content it feeds the kills is taken as explicit
hypotheses hσ / hm0; `m23_qfree` records the divisibility core).
-/

namespace ESQadicBranch1

/-- The branch-1 reduced condition bundle at modulus M with step X:
    A | X, r | X², P = X/A + 4·(X²/r) (exact ℕ division), m | P, P = m·p,
    and the two s-congruences. -/
def Branch1Bundle (M X A r m s : ℕ) : Prop :=
  ∃ P p, A ∣ X ∧ r ∣ X ^ 2 ∧ P = X / A + 4 * (X ^ 2 / r) ∧ m ∣ P ∧ P = m * p
    ∧ (s * p + X / A) ≡ 0 [MOD M] ∧ r * (s + m) ≡ 0 [MOD M]

/-- Valuation bound: q^e | q^b with q prime gives e ≤ b. -/
theorem qpow_le_of_dvd_pow {q e b : ℕ} (hq : q.Prime) (h : q ^ e ∣ q ^ b) :
    e ≤ b := by
  have hqpos : 0 < q := hq.pos
  by_contra hcon
  push_neg at hcon
  have hble : b + 1 ≤ e := hcon
  have hfac : q ^ (b + 1) ∣ q ^ e := by
    refine ⟨q ^ (e - (b + 1)), ?_⟩
    rw [← Nat.pow_add, Nat.add_sub_cancel' hble]
  have hqb1 : q ^ (b + 1) ∣ q ^ b := hfac.trans h
  have hle : q ^ (b + 1) ≤ q ^ b := Nat.le_of_dvd (pow_pos hqpos b) hqb1
  have hqq : q ^ b * q ≤ q ^ b * 1 := by
    calc q ^ b * q = q ^ (b + 1) := by rw [Nat.pow_succ]
    _ ≤ q ^ b := hle
    _ = q ^ b * 1 := by ring
  have hq1 : q ≤ 1 := Nat.le_of_mul_le_mul_left hqq (pow_pos hqpos b)
  have hq2 := hq.two_le
  omega

/-- Lemma M23′ (R111) divisibility core: s′ + m ≡ 0 (mod q) with q ∤ s′
    forces q ∤ m. -/
theorem m23_qfree {q s' m : ℕ} (hs : s' % q ≠ 0) (hσ : s' + m ≡ 0 [MOD q]) :
    ¬ q ∣ m := by
  intro hqm
  have h1 : q ∣ s' + m := Nat.modEq_zero_iff_dvd.mp hσ
  have h2 : q ∣ (s' + m) - m := Nat.dvd_sub h1 hqm
  rw [Nat.add_sub_cancel] at h2
  exact hs (Nat.dvd_iff_mod_eq_zero.mp h2)

/-- Kill (0,2): at type (α,ρ) = (0,2) the q | p squeeze contradicts the
    strict-minimum form of P′. -/
theorem kill_02 {q M₀ X₀ M' X' A A₀ r r₀ m s' : ℕ}
    (hq : q.Prime) (hq2 : ¬ q ∣ 2)
    (hqX : ¬ q ∣ X₀)
    (hM : M' = q * M₀) (hX : X' = q * X₀)
    (hAfac : A = A₀) (hA0 : ¬ q ∣ A₀) (hA0pos : 0 < A₀)
    (hrfac : r = q ^ 2 * r₀) (hr0 : ¬ q ∣ r₀) (hr0pos : 0 < r₀)
    (hs : s' % q ≠ 0) (hm0 : ¬ q ∣ m)
    (hb : Branch1Bundle M' X' A r m s')
    : False := by
  obtain ⟨P', p, hAX, hrX, hP, hmP, hPmp, hscong, _⟩ := hb
  have hqpos : 0 < q := hq.pos
  have hApos : 0 < A := by rw [hAfac]; exact hA0pos
  have hrpos : 0 < r := by rw [hrfac]; exact Nat.mul_pos (pow_pos hqpos 2) hr0pos
  -- A′ = X′/A is 0 mod q (Euclid descent of A | X′ to A | X₀)
  have hqA : ¬ q ∣ A := by rwa [hAfac]
  have hAX0 : A ∣ X₀ := by
    have hAX' : A ∣ q * X₀ := by rw [← hX]; exact hAX
    exact ESDescentTransfer.euclid_XSTEP hq hqA hAX'
  obtain ⟨k₀, hk₀⟩ := hAX0
  have hA'div : X' / A = q * k₀ := by
    have hX'fac : X' = A * (q * k₀) := by rw [hX, hk₀]; ring
    rw [hX'fac]; exact Nat.mul_div_cancel_left (q * k₀) hApos
  -- t₀ := X′²/r is q-free (t₀·r₀ = X₀²)
  obtain ⟨t₀, ht₀⟩ := hrX
  have ht₀r₀ : t₀ * r₀ = X₀ ^ 2 := by
    have hX2 : X' ^ 2 = q ^ 2 * X₀ ^ 2 := by rw [hX]; ring
    have h2 : X₀ ^ 2 = r₀ * t₀ := by
      have h1 : q ^ 2 * X₀ ^ 2 = q ^ 2 * (r₀ * t₀) := by
        calc q ^ 2 * X₀ ^ 2 = X' ^ 2 := hX2.symm
        _ = r * t₀ := ht₀
        _ = q ^ 2 * (r₀ * t₀) := by rw [hrfac]; ring
      exact Nat.mul_left_cancel (pow_pos hqpos 2) h1
    rw [h2]; ring
  have hX'div : X' ^ 2 / r = t₀ := by
    rw [ht₀]; exact Nat.mul_div_cancel_left t₀ hrpos
  -- the s-congruence forces q | p, hence q | P′
  have hqM : q ∣ M' := by rw [hM]; exact dvd_mul_right q M₀
  have hAdvd : q ∣ X' / A := by rw [hA'div]; exact dvd_mul_right q k₀
  have hqsp : q ∣ s' * p := by
    have h1 : q ∣ s' * p + X' / A := by
      have hM'dvd : M' ∣ s' * p + X' / A := Nat.modEq_zero_iff_dvd.mp hscong
      exact dvd_trans hqM hM'dvd
    have h2 : q ∣ (s' * p + X' / A) - X' / A := Nat.dvd_sub h1 hAdvd
    rwa [Nat.add_sub_cancel] at h2
  have hqp : q ∣ p := by
    rcases hq.dvd_mul.mp hqsp with h | h
    · exfalso; exact hs (Nat.dvd_iff_mod_eq_zero.mp h)
    · exact h
  have hqP : q ∣ P' := by
    rw [hPmp]; exact dvd_mul_of_dvd_right hqp m
  -- but P′ = q·k₀ + 4·t₀ has exact q-adic minimum 0
  have hq4t : q ∣ 4 * t₀ := by
    rw [hP, hA'div, hX'div] at hqP
    exact (Nat.dvd_add_iff_right (dvd_mul_right q k₀)).mpr hqP
  have hq4nd : ¬ q ∣ 4 := by
    intro h
    have h42 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h42] at h
    exact hq2 (hq.dvd_of_dvd_pow h)
  rcases hq.dvd_mul.mp hq4t with h4 | ht
  · exact hq4nd h4
  · have hqX2 : q ∣ X₀ ^ 2 := by
      rw [← ht₀r₀]; exact dvd_mul_of_dvd_left ht r₀
    exact hqX (hq.dvd_of_dvd_pow hqX2)

/-- Kill (1,2): at type (α,ρ) = (1,2) the q-adic expansion of R67's
    condition (iii) gives v_q(QQ) = −1 against QQ's integrality. -/
theorem kill_12 {q X₀ X' A A₀ r r₀ m s' x₀ : ℕ}
    (hq : q.Prime) (hq2 : ¬ q ∣ 2)
    (hqX : ¬ q ∣ X₀)
    (hX : X' = q * X₀)
    (hAfac : A = q * A₀) (hA0 : ¬ q ∣ A₀)
    (hrfac : r = q ^ 2 * r₀) (hr0 : ¬ q ∣ r₀) (hr0pos : 0 < r₀)
    (hs : s' % q ≠ 0) (hm0 : ¬ q ∣ m)
    (hσ : q ∣ s' + m)
    (hx0 : s' + m = 4 * x₀)
    (hQQ : m * A * r ∣ r * x₀ + A * s' * X')
    : False := by
  have hqpos : 0 < q := hq.pos
  have hq4nd : ¬ q ∣ 4 := by
    intro h
    have h42 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h42] at h
    exact hq2 (hq.dvd_of_dvd_pow h)
  have hcop4 : Nat.Coprime q 4 := hq.coprime_iff_not_dvd.mpr hq4nd
  -- q | (s′+m) = 4·x₀ with q ∤ 4 gives q | x₀
  have hqx0 : q ∣ x₀ := by
    have h1 : q ∣ 4 * x₀ := by rw [← hx0]; exact hσ
    exact hcop4.dvd_of_dvd_mul_left h1
  -- numerator = q²·w, denominator = q³·v₀
  have hnum : r * x₀ + A * s' * X' = q ^ 2 * (r₀ * x₀ + A₀ * s' * X₀) := by
    rw [hrfac, hAfac, hX]; ring
  have hden : m * A * r = q ^ 3 * (m * A₀ * r₀) := by
    rw [hAfac, hrfac]; ring
  rw [hnum, hden] at hQQ
  obtain ⟨k, hk⟩ := hQQ
  -- cancelling q²: q | w
  have hqw : q ∣ r₀ * x₀ + A₀ * s' * X₀ := by
    have hq2pos : 0 < q ^ 2 := pow_pos hqpos 2
    have hkk : q ^ 2 * (r₀ * x₀ + A₀ * s' * X₀)
        = q ^ 2 * (q * (m * A₀ * r₀ * k)) := by
      rw [hk]; ring
    have hcancel := Nat.mul_left_cancel hq2pos hkk
    exact ⟨m * A₀ * r₀ * k, hcancel⟩
  have hqrx : q ∣ r₀ * x₀ := dvd_mul_of_dvd_right hqx0 r₀
  have hqA : q ∣ A₀ * s' * X₀ := by
    have h2 : q ∣ (r₀ * x₀ + A₀ * s' * X₀) - r₀ * x₀ := Nat.dvd_sub hqw hqrx
    rwa [Nat.add_sub_cancel_left] at h2
  rcases hq.dvd_mul.mp hqA with h | h
  · rcases hq.dvd_mul.mp h with h1 | h1
    · exact hA0 h1
    · exfalso; exact hs (Nat.dvd_iff_mod_eq_zero.mp h1)
  · exact hqX h

/-- Kill (0,1): at type (α,ρ) = (0,1) the identity descends to a full
    branch-1 bundle at M₀ on s₀ (exact q-cancellation P′ = q·P₀). -/
theorem descent_01 {q M₀ X₀ M' X' A A₀ r r₀ m s' s₀ j : ℕ}
    (hq : q.Prime)
    (hM : M' = q * M₀) (hX : X' = q * X₀)
    (hAfac : A = A₀) (hA0 : ¬ q ∣ A₀) (hA0pos : 0 < A₀)
    (hrfac : r = q * r₀) (hr0 : ¬ q ∣ r₀) (hr0pos : 0 < r₀)
    (hmpos : 0 < m) (hm0 : ¬ q ∣ m)
    (hs' : s' = s₀ + M₀ * j)
    (hb : Branch1Bundle M' X' A r m s')
    : Branch1Bundle M₀ X₀ A₀ r₀ m s₀ := by
  obtain ⟨P', p, hAX, hrX, hP, hmP, hPmp, hscong, hrcong⟩ := hb
  have hqpos : 0 < q := hq.pos
  have hApos : 0 < A := by rw [hAfac]; exact hA0pos
  have hrpos : 0 < r := by rw [hrfac]; exact Nat.mul_pos hqpos hr0pos
  -- A-part: A | X₀, X₀/A₀ = k₀, X′/A = q·k₀
  have hqA : ¬ q ∣ A := by rwa [hAfac]
  have hAX0 : A ∣ X₀ := by
    have hAX' : A ∣ q * X₀ := by rw [← hX]; exact hAX
    exact ESDescentTransfer.euclid_XSTEP hq hqA hAX'
  obtain ⟨k₀, hk₀⟩ := hAX0
  have hA0k₀ : X₀ = A₀ * k₀ := by rw [hAfac] at hk₀; exact hk₀
  have hXdiv : X' / A = q * k₀ := by
    have hX'fac : X' = A * (q * k₀) := by rw [hX, hk₀]; ring
    rw [hX'fac]; exact Nat.mul_div_cancel_left (q * k₀) hApos
  have hX0div : X₀ / A₀ = k₀ := by
    rw [hA0k₀]; exact Nat.mul_div_cancel_left k₀ hA0pos
  -- r-part: r₀ | X₀², X₀²/r₀ = t₂, X′²/r = q·t₂
  obtain ⟨t₁, ht₁⟩ := hrX
  have hqrt : q ∣ r₀ * t₁ := by
    have hX2 : X' ^ 2 = q ^ 2 * X₀ ^ 2 := by rw [hX]; ring
    have h1 : q * (q * X₀ ^ 2) = q * (r₀ * t₁) := by
      calc q * (q * X₀ ^ 2) = q ^ 2 * X₀ ^ 2 := by ring
      _ = X' ^ 2 := hX2.symm
      _ = r * t₁ := ht₁
      _ = q * (r₀ * t₁) := by rw [hrfac]; ring
    have h2 := Nat.mul_left_cancel hqpos h1
    exact ⟨X₀ ^ 2, h2.symm⟩
  have hqt₁ : q ∣ t₁ := by
    rcases hq.dvd_mul.mp hqrt with h | h
    · exact absurd h hr0
    · exact h
  obtain ⟨t₂, ht₂⟩ := hqt₁
  have ht₂X : X₀ ^ 2 = r₀ * t₂ := by
    have hX2 : X' ^ 2 = q ^ 2 * X₀ ^ 2 := by rw [hX]; ring
    have h1 : q ^ 2 * (r₀ * t₂) = q ^ 2 * X₀ ^ 2 := by
      calc q ^ 2 * (r₀ * t₂) = (q * r₀) * (q * t₂) := by ring
      _ = r * t₁ := by rw [hrfac, ht₂]
      _ = X' ^ 2 := ht₁.symm
      _ = q ^ 2 * X₀ ^ 2 := hX2
    exact (Nat.mul_left_cancel (pow_pos hqpos 2) h1).symm
  have hr0X : r₀ ∣ X₀ ^ 2 := ⟨t₂, ht₂X⟩
  have hX02div : X₀ ^ 2 / r₀ = t₂ := by
    rw [ht₂X]; exact Nat.mul_div_cancel_left t₂ hr0pos
  have hX2div : X' ^ 2 / r = q * t₂ := by
    have hX'fac : X' ^ 2 = r * (q * t₂) := by rw [ht₁, ht₂]
    rw [hX'fac]; exact Nat.mul_div_cancel_left (q * t₂) hrpos
  -- P-part: P′ = q·P₀, m | P₀ (m coprime to q), p = q·p₁
  have hPq : P' = q * (k₀ + 4 * t₂) := by rw [hP, hXdiv, hX2div]; ring
  have hcm : Nat.Coprime m q := (hq.coprime_iff_not_dvd.mpr hm0).symm
  have hmPdesc : m ∣ k₀ + 4 * t₂ := by
    have h1 : m ∣ q * (k₀ + 4 * t₂) := by rw [← hPq]; exact hmP
    exact hcm.dvd_of_dvd_mul_left h1
  obtain ⟨p₁, hp₁⟩ := hmPdesc
  have hpp₁ : p = q * p₁ := by
    have h1 : m * p = m * (q * p₁) := by rw [← hPmp, hPq, hp₁]; ring
    exact Nat.mul_left_cancel hmpos h1
  -- descended s-congruence
  have hdscong : M₀ ∣ s' * p₁ + k₀ := by
    have h1 : M' ∣ s' * p + X' / A := Nat.modEq_zero_iff_dvd.mp hscong
    rw [hM, hXdiv, hpp₁] at h1
    have h2 : s' * (q * p₁) + q * k₀ = q * (s' * p₁ + k₀) := by ring
    rw [h2] at h1
    exact (Nat.mul_dvd_mul_iff_left hqpos).mp h1
  have hds₀ : M₀ ∣ s₀ * p₁ + k₀ := by
    have hdiff : s' * p₁ + k₀ = (s₀ * p₁ + k₀) + M₀ * (j * p₁) := by rw [hs']; ring
    rw [hdiff] at hdscong
    exact (Nat.dvd_add_iff_left (dvd_mul_right M₀ (j * p₁))).mpr hdscong
  -- descended r-congruence
  have hr3 : M₀ ∣ r₀ * (s' + m) := by
    have h1 : M' ∣ r * (s' + m) := Nat.modEq_zero_iff_dvd.mp hrcong
    rw [hM, hrfac] at h1
    have h2 : q * r₀ * (s' + m) = q * (r₀ * (s' + m)) := by ring
    rw [h2] at h1
    exact (Nat.mul_dvd_mul_iff_left hqpos).mp h1
  have hdr₀ : M₀ ∣ r₀ * (s₀ + m) := by
    have hdiff : r₀ * (s' + m) = r₀ * (s₀ + m) + M₀ * (j * r₀) := by rw [hs']; ring
    rw [hdiff] at hr3
    exact (Nat.dvd_add_iff_left (dvd_mul_right M₀ (j * r₀))).mpr hr3
  -- assemble the descended bundle (P := k₀ + 4·t₂, p := p₁)
  -- (hmPdesc was consumed by the obtain above; rebuild m ∣ P₀ from ⟨p₁, hp₁⟩)
  refine ⟨k₀ + 4 * t₂, p₁, ⟨k₀, hA0k₀⟩, hr0X, ?_, ⟨p₁, hp₁⟩, hp₁, ?_, ?_⟩
  · rw [hX0div, hX02div]
  · rw [hX0div]; exact Nat.modEq_zero_iff_dvd.mpr hds₀
  · exact Nat.modEq_zero_iff_dvd.mpr hdr₀

/-- The branch-1 q-adic type theorem (R116 §A): every branch-1 cubic
    identity at M′ = q·M₀ (q odd prime, q ∤ M₀) on a refined target s′
    satisfies (v_q(A), v_q(r)) ∈ {(0,0), (1,0), (1,1)}.

    `hR74` is the R74 complete-sweep input (no descended branch-1 bundle
    exists at M₀); `hQQ` is R67's condition (iii) (QQ integrality). -/
theorem qadic_type_restriction {q M₀ X₀ M' X' A A₀ r r₀ m s' x₀ : ℕ} (α ρ : ℕ)
    (hq : q.Prime) (hq2 : ¬ q ∣ 2)
    (hqX : ¬ q ∣ X₀)
    (hM : M' = q * M₀) (hX : X' = q * X₀)
    (hAfac : A = q ^ α * A₀) (hA0 : ¬ q ∣ A₀) (hA0pos : 0 < A₀)
    (hrfac : r = q ^ ρ * r₀) (hr0 : ¬ q ∣ r₀) (hr0pos : 0 < r₀)
    (hmpos : 0 < m)
    (hs : s' % q ≠ 0) (hm0 : ¬ q ∣ m)
    (hσ : q ∣ s' + m)
    (hx0 : s' + m = 4 * x₀)
    (hb : Branch1Bundle M' X' A r m s')
    (hQQ : m * A * r ∣ r * x₀ + A * s' * X')
    (hR74 : ∀ s₀ j, s' = s₀ + M₀ * j → ¬ Branch1Bundle M₀ X₀ A₀ r₀ m s₀)
    : (α = 0 ∧ ρ = 0) ∨ (α = 1 ∧ ρ = 0) ∨ (α = 1 ∧ ρ = 1) := by
  have hAX : A ∣ X' := by obtain ⟨_, _, hAX, _, _, _, _, _, _⟩ := hb; exact hAX
  have hrX : r ∣ X' ^ 2 := by obtain ⟨_, _, _, hrX, _, _, _, _, _⟩ := hb; exact hrX
  -- valuation bounds from the divisor data
  have hα : α ≤ 1 := by
    have hAX' : A ∣ q * X₀ := by rw [← hX]; exact hAX
    have hqαdvd : q ^ α ∣ q := by
      have h1 : q ^ α ∣ A := ⟨A₀, by rw [hAfac]⟩
      have h2 : q ^ α ∣ q * X₀ := h1.trans hAX'
      have hcop : Nat.Coprime (q ^ α) X₀ := (hq.coprime_iff_not_dvd.mpr hqX).pow_left α
      exact hcop.dvd_of_dvd_mul_right h2
    exact qpow_le_of_dvd_pow hq (by rwa [pow_one])
  have hρ : ρ ≤ 2 := by
    have hX2 : X' ^ 2 = q ^ 2 * X₀ ^ 2 := by rw [hX]; ring
    have hrX' : r ∣ q ^ 2 * X₀ ^ 2 := by rw [← hX2]; exact hrX
    have hqρdvd : q ^ ρ ∣ q ^ 2 := by
      have h1 : q ^ ρ ∣ r := ⟨r₀, by rw [hrfac]⟩
      have h2 : q ^ ρ ∣ q ^ 2 * X₀ ^ 2 := h1.trans hrX'
      have hcop : Nat.Coprime (q ^ ρ) (X₀ ^ 2) :=
        ((hq.coprime_iff_not_dvd.mpr hqX).pow_left ρ).pow_right 2
      exact hcop.dvd_of_dvd_mul_right h2
    exact qpow_le_of_dvd_pow hq hqρdvd
  have hα01 : α = 0 ∨ α = 1 := by omega
  have hρ012 : ρ = 0 ∨ ρ = 1 ∨ ρ = 2 := by omega
  have hs'split : s' = s' + M₀ * 0 := by simp
  rcases hα01 with rfl | rfl <;> rcases hρ012 with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · -- (0,1): descent to M₀, barred by the R74 input
    exfalso
    have hAfac0 : A = A₀ := by simpa using hAfac
    have hrfac1 : r = q * r₀ := by simpa using hrfac
    exact hR74 s' 0 hs'split
      (descent_01 hq hM hX hAfac0 hA0 hA0pos hrfac1 hr0 hr0pos hmpos hm0 hs'split hb)
  · -- (0,2): killed by kill_02
    exfalso
    have hAfac0 : A = A₀ := by simpa using hAfac
    exact kill_02 hq hq2 hqX hM hX hAfac0 hA0 hA0pos hrfac hr0 hr0pos hs hm0 hb
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · -- (1,2): killed by kill_12
    exfalso
    have hAfac1 : A = q * A₀ := by simpa using hAfac
    exact kill_12 hq hq2 hqX hX hAfac1 hA0 hrfac hr0 hr0pos hs hm0 hσ hx0 hQQ

end ESQadicBranch1
