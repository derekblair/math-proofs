import Mathproofs.ESQadicBranch1

/-!
# What branch-1 q-adic classification proves without the R74 sweep

The divisor bounds and the two valuation contradictions imply `α ≤ 1` and
`ρ ≤ 1` without a sweep hypothesis. The remaining type `(0,1)` can actually
occur for the generic hypotheses: the explicit example below has `q = 3`,
`M₀ = 4`, `X₀ = 1`, `M′ = 12`, `X′ = 3`, and a full branch-1 bundle.

This is a boundary result for the generic theorem. It does not refute the
paper's fixed modulus `2042040` and its separately specified refined targets.
QQ integrality and `q ∣ s′ + m` remain explicit hypotheses; no unavailable
sweep data or target-classification result is supplied here.
-/

namespace ESQadicBranch1

/-- Divisor data alone give the two initial valuation bounds. -/
theorem branch1_valuation_bounds {q M' X₀ X' A A₀ r r₀ m s' : ℕ} (α ρ : ℕ)
    (hq : q.Prime) (hqX : ¬ q ∣ X₀) (hX : X' = q * X₀)
    (hAfac : A = q ^ α * A₀) (hrfac : r = q ^ ρ * r₀)
    (hb : Branch1Bundle M' X' A r m s') : α ≤ 1 ∧ ρ ≤ 2 := by
  obtain ⟨_, _, hAX, hrX, _⟩ := hb
  constructor
  · have hAX' : A ∣ q * X₀ := by rw [← hX]; exact hAX
    have hqαdvd : q ^ α ∣ q := by
      have h1 : q ^ α ∣ A := ⟨A₀, by rw [hAfac]⟩
      have h2 : q ^ α ∣ q * X₀ := h1.trans hAX'
      have hcop : Nat.Coprime (q ^ α) X₀ :=
        (hq.coprime_iff_not_dvd.mpr hqX).pow_left α
      exact hcop.dvd_of_dvd_mul_right h2
    exact qpow_le_of_dvd_pow hq (by rwa [pow_one])
  · have hX2 : X' ^ 2 = q ^ 2 * X₀ ^ 2 := by rw [hX]; ring
    have hrX' : r ∣ q ^ 2 * X₀ ^ 2 := by rw [← hX2]; exact hrX
    have hqρdvd : q ^ ρ ∣ q ^ 2 := by
      have h1 : q ^ ρ ∣ r := ⟨r₀, by rw [hrfac]⟩
      have h2 : q ^ ρ ∣ q ^ 2 * X₀ ^ 2 := h1.trans hrX'
      have hcop : Nat.Coprime (q ^ ρ) (X₀ ^ 2) :=
        ((hq.coprime_iff_not_dvd.mpr hqX).pow_left ρ).pow_right 2
      exact hcop.dvd_of_dvd_mul_right h2
    exact qpow_le_of_dvd_pow hq hqρdvd

/-- The part of the generic classification independent of the sweep: both exponents are
at most one. There is no `hR74` premise, and `q ∤ m` is derived from M23's core. -/
theorem qadic_type_bounds_without_sweep
    {q M₀ X₀ M' X' A A₀ r r₀ m s' x₀ : ℕ} (α ρ : ℕ)
    (hq : q.Prime) (hq2 : ¬ q ∣ 2) (hqX : ¬ q ∣ X₀)
    (hM : M' = q * M₀) (hX : X' = q * X₀)
    (hAfac : A = q ^ α * A₀) (hA0 : ¬ q ∣ A₀) (hA0pos : 0 < A₀)
    (hrfac : r = q ^ ρ * r₀) (hr0 : ¬ q ∣ r₀) (hr0pos : 0 < r₀)
    (hs : s' % q ≠ 0) (hσ : q ∣ s' + m) (hx0 : s' + m = 4 * x₀)
    (hb : Branch1Bundle M' X' A r m s')
    (hQQ : m * A * r ∣ r * x₀ + A * s' * X') : α ≤ 1 ∧ ρ ≤ 1 := by
  obtain ⟨hα, hρ⟩ := branch1_valuation_bounds α ρ hq hqX hX hAfac hrfac hb
  have hm0 : ¬ q ∣ m := m23_qfree hs (Nat.modEq_zero_iff_dvd.mpr hσ)
  refine ⟨hα, ?_⟩
  by_contra hrgt
  have hρ2 : ρ = 2 := by omega
  have hα01 : α = 0 ∨ α = 1 := by omega
  subst ρ
  rcases hα01 with hα0 | hα1
  · have hAfac0 : A = A₀ := by simpa [hα0] using hAfac
    exact kill_02 hq hq2 hqX hM hX hAfac0 hA0 hA0pos hrfac hr0 hr0pos hs hm0 hb
  · have hAfac1 : A = q * A₀ := by simpa [hα1] using hAfac
    exact kill_12 hq hq2 hqX hX hAfac1 hA0 hrfac hr0 hr0pos hs hm0 hσ hx0 hQQ

/-- The original three-type classification with its genuine sweep premise,
but with the redundant `q ∤ m` input discharged by `m23_qfree`. -/
theorem qadic_type_restriction_from_m23
    {q M₀ X₀ M' X' A A₀ r r₀ m s' x₀ : ℕ} (α ρ : ℕ)
    (hq : q.Prime) (hq2 : ¬ q ∣ 2) (hqX : ¬ q ∣ X₀)
    (hM : M' = q * M₀) (hX : X' = q * X₀)
    (hAfac : A = q ^ α * A₀) (hA0 : ¬ q ∣ A₀) (hA0pos : 0 < A₀)
    (hrfac : r = q ^ ρ * r₀) (hr0 : ¬ q ∣ r₀) (hr0pos : 0 < r₀)
    (hmpos : 0 < m) (hs : s' % q ≠ 0) (hσ : q ∣ s' + m)
    (hx0 : s' + m = 4 * x₀) (hb : Branch1Bundle M' X' A r m s')
    (hQQ : m * A * r ∣ r * x₀ + A * s' * X')
    (hR74 : ∀ s₀ j, s' = s₀ + M₀ * j → ¬ Branch1Bundle M₀ X₀ A₀ r₀ m s₀) :
    (α = 0 ∧ ρ = 0) ∨ (α = 1 ∧ ρ = 0) ∨ (α = 1 ∧ ρ = 1) := by
  have hm0 : ¬ q ∣ m := m23_qfree hs (Nat.modEq_zero_iff_dvd.mpr hσ)
  exact qadic_type_restriction α ρ hq hq2 hqX hM hX hAfac hA0 hA0pos
    hrfac hr0 hr0pos hmpos hs hm0 hσ hx0 hb hQQ hR74

/-- Explicit type-(0,1) bundle: `P = p = 15`. -/
theorem type01_bundle : Branch1Bundle 12 3 1 3 1 11 := by
  refine ⟨15, 15, ?_⟩
  norm_num [Nat.ModEq]

/-- This example descends to the base modulus with canonical target `3`. -/
theorem type01_descended_bundle : Branch1Bundle 4 1 1 1 1 3 := by
  exact descent_01 (q := 3) (M' := 12) (X' := 3) (A := 1) (r := 3)
    (s' := 11) (j := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) type01_bundle

/-- Accordingly the sweep exclusion is false for this generic example. -/
theorem type01_sweep_exclusion_false :
    ¬ (∀ s₀ j, 11 = s₀ + 4 * j → ¬ Branch1Bundle 4 1 1 1 1 s₀) := by
  intro h
  exact h 3 2 (by norm_num) type01_descended_bundle

/-- All generic inputs except the sweep exclusion can hold at type `(0,1)`.
This is a counterexample to deleting `hR74` from the generic theorem, not to
the fixed-modulus/refined-target theorem described by the manuscript. -/
theorem generic_type01_counterexample :
    ∃ q M₀ X₀ M' X' A A₀ r r₀ m s' x₀ α ρ : ℕ,
      q.Prime ∧ ¬ q ∣ 2 ∧ ¬ q ∣ M₀ ∧ M₀ = 4 * X₀ ∧ ¬ q ∣ X₀ ∧
      M' = q * M₀ ∧ X' = q * X₀ ∧ s' < M' ∧
      A = q ^ α * A₀ ∧ ¬ q ∣ A₀ ∧ 0 < A₀ ∧
      r = q ^ ρ * r₀ ∧ ¬ q ∣ r₀ ∧ 0 < r₀ ∧ 0 < m ∧
      s' % q ≠ 0 ∧ ¬ q ∣ m ∧ q ∣ s' + m ∧ s' + m = 4 * x₀ ∧
      Branch1Bundle M' X' A r m s' ∧
      m * A * r ∣ r * x₀ + A * s' * X' ∧
      ¬ ((α = 0 ∧ ρ = 0) ∨ (α = 1 ∧ ρ = 0) ∨ (α = 1 ∧ ρ = 1)) := by
  refine ⟨3, 4, 1, 12, 3, 1, 1, 3, 1, 1, 11, 3, 0, 1, ?_⟩
  norm_num [type01_bundle]

end ESQadicBranch1
