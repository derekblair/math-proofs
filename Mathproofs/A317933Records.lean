import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Seam B Entry C047 (OEIS A317933): Karttunen Dirichlet-Square-Root Numerator Records

Formalizes and proves Antti Karttunen's record conjecture on `OEIS A317933` (`%C` line 13:
*"Records seem to be A001790, occurring at A000302 (apart from 4)"*) against frozen manifest
`PIN-C047.md` v1 (`delta_vs_source: NONE`), following the power-series-free and logarithm-free
derivation chain `D1–D8` from `SCOPING-C047.md` §2.2:

* **D1 (`dirichlet_sqrt_unique`):** Uniqueness of the normalized Dirichlet square root
  `h 1 = 1 ∧ h * h = u` by strong induction on `n` over `Nat.divisorsAntidiagonal`.
* **D2a (`centralBinom_conv`):** Finite sum-reversal proof of
  `∑ i ∈ Finset.range (m + 1), B_i * B_{m - i} = 4 ^ m`.
* **D2b (`g`, `g_isMultiplicative`, `g_mul_self_eq_u`, `g_eq_f`):** Computable multiplicative
  witness `g` on `ℚ` satisfying `g 1 = 1 ∧ g * g = u` via parity-split prime-power sums,
  discharging `f_existsUnique` and identifying `f = g`.
* **D3 (`centralBinom_factorization_two`, `A001790_coprime_two`):** Legendre/Kummer 2-adic
  valuation `v_2(B_m) = (Nat.digits 2 m).sum`, exact division `2 ^ s(m) * A001790 m = B_m`, and
  oddness (`Coprime _ 2`) of `A001790 m`.
* **D4 (`A001790_eq_num`, `a_eq_prod_A001790`, `a_prime_pow`):** `Rat.num` no-cancellation
  bridge (`Finset.prod_div_distrib` + `Rat.num_div_eq_of_coprime`), proving both `A001790_eq_num`
  and Amiram Eldar's Nov 01 2026 formula `a (p ^ e) = A001790 (e / 2)` from first principles.
* **D5–D6 (`s2_add_le`, `A001790_strictMono_from_one`, `A001790_supermult`):** Binary digit-sum
  subadditivity, strict monotonicity of `A001790` for `k ≥ 1`, and exact `ℕ`
  supermultiplicativity `A001790 x * A001790 y ≤ A001790 (x + y)` via Vandermonde
  (together with `triage_step2_bound_false_at_31` refuting the naive intermediate bound at `k = 31`).
* **D7–D8 (`four_pow_M_le`, `a317933_records`):** Exponent-sum dominance `4 ^ M(n) ≤ n` and the
  complete two-way characterization of strict 1-based prefix records and record values, plus
  kernel-checked non-vacuity and guard-sharpness theorems.
-/

namespace Mathproofs.A317933Records

def u : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else (2 : ℚ) ^ n.primeFactors.card, by simp⟩

noncomputable def f : ArithmeticFunction ℚ :=
  open Classical in
  if h : ∃ g : ArithmeticFunction ℚ, g 1 = 1 ∧ g * g = u then Classical.choose h else 0

noncomputable def a (n : ℕ) : ℤ := (f n).num

def A001790 (k : ℕ) : ℕ := Nat.choose (2 * k) k / 2 ^ (Nat.digits 2 k).sum

def isStrictRecord (seq : ℕ → ℤ) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → m < n → seq m < seq n

/-! ### Step D1: Uniqueness of the Normalized Dirichlet Square Root -/

theorem dirichlet_sqrt_apply_ge_two {h : ArithmeticFunction ℚ} (hh1 : h 1 = 1) {n : ℕ}
    (hn : 2 ≤ n) :
    (h * h) n =
      2 * h n +
        ∑ x ∈ (n.divisorsAntidiagonal.erase (1, n)).erase (n, 1), h x.1 * h x.2 := by
  rw [ArithmeticFunction.mul_apply]
  have hm1 : (1, n) ∈ n.divisorsAntidiagonal := by
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨one_mul n, by omega⟩
  have hm2 : (n, 1) ∈ n.divisorsAntidiagonal.erase (1, n) := by
    rw [Finset.mem_erase, Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, mul_one n, by omega⟩
    intro heq
    injection heq with h1 _
    omega
  rw [← Finset.add_sum_erase _ _ hm1, ← Finset.add_sum_erase _ _ hm2]
  simp only [hh1, one_mul, mul_one]
  ring

theorem dirichlet_sqrt_unique {h₁ h₂ : ArithmeticFunction ℚ}
    (hh₁ : h₁ 1 = 1 ∧ h₁ * h₁ = u) (hh₂ : h₂ 1 = 1 ∧ h₂ * h₂ = u) : h₁ = h₂ := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [hh₁.1, hh₂.1]
    have hn2 : 2 ≤ n := by omega
    have hsum :
        ∑ x ∈ (n.divisorsAntidiagonal.erase (1, n)).erase (n, 1), h₁ x.1 * h₁ x.2 =
          ∑ x ∈ (n.divisorsAntidiagonal.erase (1, n)).erase (n, 1), h₂ x.1 * h₂ x.2 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_erase] at hx
      obtain ⟨hxn1, hx'⟩ := hx
      rw [Finset.mem_erase, Nat.mem_divisorsAntidiagonal] at hx'
      obtain ⟨hx1n, hmul, _⟩ := hx'
      have hx1_pos : 0 < x.1 := by
        rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
        · exfalso; rw [h0, zero_mul] at hmul; omega
        · exact hpos
      have hx2_pos : 0 < x.2 := by
        rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
        · exfalso; rw [h0, mul_zero] at hmul; omega
        · exact hpos
      have hx1_lt : x.1 < n := by
        have hle : x.1 ≤ n := by
          rw [← hmul]
          exact Nat.le_mul_of_pos_right x.1 hx2_pos
        rcases eq_or_lt_of_le hle with h_eq | h_lt
        · exfalso
          have hx2_eq : x.2 = 1 := by
            have h1 : x.1 * x.2 = n * 1 := by rw [hmul, mul_one]
            rw [h_eq] at h1
            exact Nat.eq_of_mul_eq_mul_left (by omega) h1
          apply hxn1
          cases x
          simp only at h_eq hx2_eq
          subst h_eq; subst hx2_eq; rfl
        · exact h_lt
      have hx2_lt : x.2 < n := by
        have hle : x.2 ≤ n := by
          rw [← hmul]
          exact Nat.le_mul_of_pos_left x.2 hx1_pos
        rcases eq_or_lt_of_le hle with h_eq | h_lt
        · exfalso
          have hx1_eq : x.1 = 1 := by
            have h1 : x.1 * x.2 = 1 * n := by rw [hmul, one_mul]
            rw [h_eq] at h1
            exact Nat.eq_of_mul_eq_mul_right (by omega) h1
          apply hx1n
          cases x
          simp only at h_eq hx1_eq
          subst h_eq; subst hx1_eq; rfl
        · exact h_lt
      rw [ih x.1 hx1_lt, ih x.2 hx2_lt]
    have heq : (h₁ * h₁) n = (h₂ * h₂) n := by rw [hh₁.2, hh₂.2]
    rw [dirichlet_sqrt_apply_ge_two hh₁.1 hn2, dirichlet_sqrt_apply_ge_two hh₂.1 hn2, hsum] at heq
    linarith

/-! ### Step D2a: Finite Sum-Reversal Proof of Central-Binomial Self-Convolution -/

def cbConv (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (m + 1), Nat.centralBinom i * Nat.centralBinom (m - i)

theorem centralBinom_conv (m : ℕ) : cbConv m = 4 ^ m := by
  induction m with
  | zero => simp [cbConv]
  | succ m ih =>
    have href1 :
        ∑ k ∈ Finset.range (m + 2),
            (m + 1 - k) * (Nat.centralBinom k * Nat.centralBinom (m + 1 - k)) =
          ∑ k ∈ Finset.range (m + 2),
            k * (Nat.centralBinom k * Nat.centralBinom (m + 1 - k)) := by
      have hr :=
        Finset.sum_range_reflect
          (fun k => k * (Nat.centralBinom k * Nat.centralBinom (m + 1 - k))) (m + 2)
      rw [show m + 2 - 1 = m + 1 by omega] at hr
      rw [← hr]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hle : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Nat.sub_sub_self hle, mul_comm (Nat.centralBinom k)]
    have hstep1 :
        (m + 1) * cbConv (m + 1) =
          2 * ∑ k ∈ Finset.range (m + 2),
            k * (Nat.centralBinom k * Nat.centralBinom (m + 1 - k)) := by
      rw [two_mul]
      nth_rw 1 [← href1]
      rw [← Finset.sum_add_distrib, cbConv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hle : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [← add_mul, Nat.sub_add_cancel hle]
    have hstep2 :
        ∑ k ∈ Finset.range (m + 2),
            k * (Nat.centralBinom k * Nat.centralBinom (m + 1 - k)) =
          2 * ∑ j ∈ Finset.range (m + 1),
            (2 * j + 1) * (Nat.centralBinom j * Nat.centralBinom (m - j)) := by
      rw [Finset.sum_range_succ', zero_mul, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hcb := Nat.succ_mul_centralBinom_succ j
      rw [Nat.succ_sub_succ_eq_sub]
      calc
        (j + 1) * (Nat.centralBinom (j + 1) * Nat.centralBinom (m - j))
          = ((j + 1) * Nat.centralBinom (j + 1)) * Nat.centralBinom (m - j) := by ring
        _ = (2 * (2 * j + 1) * Nat.centralBinom j) * Nat.centralBinom (m - j) := by rw [hcb]
        _ = 2 * ((2 * j + 1) * (Nat.centralBinom j * Nat.centralBinom (m - j))) := by ring
    have href2 :
        ∑ j ∈ Finset.range (m + 1),
            (2 * (m - j) + 1) * (Nat.centralBinom j * Nat.centralBinom (m - j)) =
          ∑ j ∈ Finset.range (m + 1),
            (2 * j + 1) * (Nat.centralBinom j * Nat.centralBinom (m - j)) := by
      have hr :=
        Finset.sum_range_reflect
          (fun j => (2 * j + 1) * (Nat.centralBinom j * Nat.centralBinom (m - j))) (m + 1)
      rw [show m + 1 - 1 = m by omega] at hr
      rw [← hr]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Nat.sub_sub_self hle, mul_comm (Nat.centralBinom j)]
    have hstep3 :
        2 * ∑ j ∈ Finset.range (m + 1),
            (2 * j + 1) * (Nat.centralBinom j * Nat.centralBinom (m - j)) =
          2 * (m + 1) * cbConv m := by
      rw [two_mul]
      nth_rw 1 [← href2]
      rw [← Finset.sum_add_distrib, cbConv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hlin : (2 * (m - j) + 1) + (2 * j + 1) = 2 * (m + 1) := by omega
      rw [← add_mul, hlin]
    have hmul : (m + 1) * cbConv (m + 1) = (m + 1) * (4 * cbConv m) := by
      calc
        (m + 1) * cbConv (m + 1)
          = 2 * (2 * ∑ j ∈ Finset.range (m + 1),
              (2 * j + 1) * (Nat.centralBinom j * Nat.centralBinom (m - j))) := by
            rw [hstep1, hstep2]
        _ = 2 * (2 * (m + 1) * cbConv m) := by rw [hstep3]
        _ = (m + 1) * (4 * cbConv m) := by ring
    have hcanc := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) hmul
    rw [hcanc, ih, pow_succ']

theorem centralBinom_conv_rat (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1),
      ((Nat.centralBinom i : ℚ) / (4 : ℚ) ^ i) *
        ((Nat.centralBinom (m - i) : ℚ) / (4 : ℚ) ^ (m - i))) = 1 := by
  have h4pos : (0 : ℚ) < (4 : ℚ) ^ m := by positivity
  have hmul :
      (∑ i ∈ Finset.range (m + 1),
        ((Nat.centralBinom i : ℚ) / (4 : ℚ) ^ i) *
          ((Nat.centralBinom (m - i) : ℚ) / (4 : ℚ) ^ (m - i))) * (4 : ℚ) ^ m =
        (∑ i ∈ Finset.range (m + 1),
          ((Nat.centralBinom i * Nat.centralBinom (m - i) : ℕ) : ℚ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hle : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h4m : (4 : ℚ) ^ m ≠ 0 := h4pos.ne'
    rw [div_mul_div_comm, ← pow_add, Nat.add_sub_of_le hle, div_mul_cancel₀ _ h4m, Nat.cast_mul]
  rw [← Nat.cast_sum, ← cbConv, centralBinom_conv, Nat.cast_pow, Nat.cast_ofNat] at hmul
  exact (mul_left_inj' h4pos.ne').mp (by rw [hmul, one_mul])

/-! ### Step D2b: Computable Multiplicative Witness `g` and Prime-Power Convolution -/

def localFactor (e : ℕ) : ℚ :=
  (Nat.centralBinom (e / 2) : ℚ) / (4 : ℚ) ^ (e / 2)

@[simp]
theorem localFactor_zero : localFactor 0 = 1 := by
  simp [localFactor]

theorem localFactor_two_mul (i : ℕ) :
    localFactor (2 * i) = (Nat.centralBinom i : ℚ) / (4 : ℚ) ^ i := by
  simp [localFactor]

theorem localFactor_two_mul_add_one (i : ℕ) :
    localFactor (2 * i + 1) = (Nat.centralBinom i : ℚ) / (4 : ℚ) ^ i := by
  have hdiv : (2 * i + 1) / 2 = i := by omega
  simp [localFactor, hdiv]

/-- Explicit computable Dirichlet square root of `u` (`SCOPING-C047.md` §2.2 Step D2). -/
def g : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else ∏ p ∈ n.primeFactors, localFactor (n.factorization p), by simp⟩

theorem g_apply_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    g n = ∏ p ∈ n.primeFactors, localFactor (n.factorization p) := by
  simp [g, hn]

theorem u_apply_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    u n = (2 : ℚ) ^ n.primeFactors.card := by
  simp [u, hn]

theorem u_isMultiplicative : u.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [u], ?_⟩
  intro x y hx hy hxy
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx hy
  rw [u_apply_of_ne_zero hxy0, u_apply_of_ne_zero hx, u_apply_of_ne_zero hy,
    Nat.primeFactors_mul hx hy, Finset.card_union_of_disjoint hxy.disjoint_primeFactors, pow_add]

theorem g_one : g 1 = 1 := by
  simp [g]

theorem g_isMultiplicative : g.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨g_one, ?_⟩
  intro x y hx hy hxy
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx hy
  rw [g_apply_of_ne_zero hxy0, g_apply_of_ne_zero hx, g_apply_of_ne_zero hy,
    Nat.primeFactors_mul hx hy, Finset.prod_union hxy.disjoint_primeFactors]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hp_not_y : p ∉ y.primeFactors := Finset.disjoint_left.mp hxy.disjoint_primeFactors hp
    have hy_zero : y.factorization p = 0 := Finsupp.notMem_support_iff.mp hp_not_y
    rw [Nat.factorization_mul hx hy, Finsupp.add_apply, hy_zero, add_zero]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hp_not_x : p ∉ x.primeFactors := Finset.disjoint_right.mp hxy.disjoint_primeFactors hp
    have hx_zero : x.factorization p = 0 := Finsupp.notMem_support_iff.mp hp_not_x
    rw [Nat.factorization_mul hx hy, Finsupp.add_apply, hx_zero, zero_add]

theorem g_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) : g (p ^ e) = localFactor e := by
  rw [g_apply_of_ne_zero (pow_ne_zero e hp.ne_zero),
    ← Nat.prod_factorization_eq_prod_primeFactors (fun _ k => localFactor k),
    hp.factorization_pow, Finsupp.prod_single_index (by simp)]

theorem u_prime_pow_pos {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) : u (p ^ e) = 2 := by
  have hne : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  have hpf : (p ^ e).primeFactors = {p} := by
    rw [← Nat.support_factorization, hp.factorization_pow]
    simp [Finsupp.support_single, he]
  rw [u_apply_of_ne_zero hne, hpf, Finset.card_singleton, pow_one]

theorem sum_range_pair {M : Type*} [AddCommMonoid M] (h : ℕ → M) (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m + 2), h j =
      ∑ i ∈ Finset.range (m + 1), (h (2 * i) + h (2 * i + 1)) := by
  induction m with
  | zero =>
    simp [Finset.sum_range_succ]
  | succ m ih =>
    rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ (fun i => h (2 * i) + h (2 * i + 1)) (m + 1), add_assoc]
    simp [Nat.mul_add]

theorem localFactor_conv_eq_two {e : ℕ} (he : e ≠ 0) :
    ∑ j ∈ Finset.range (e + 1), localFactor j * localFactor (e - j) = 2 := by
  rcases Nat.even_or_odd' e with ⟨m, rfl | rfl⟩
  · -- Case `e = 2 * m` (`m ≥ 1` since `e ≠ 0`)
    rcases m with _ | m
    · simp at he
    -- Now `e = 2 * (m + 1) = 2 * m + 2`
    rw [show 2 * (m + 1) = 2 * m + 2 by omega]
    rw [Finset.sum_range_succ, sum_range_pair, Finset.sum_add_distrib]
    have htop :
        localFactor (2 * m + 2) * localFactor (2 * m + 2 - (2 * m + 2)) =
          ((Nat.centralBinom (m + 1) : ℚ) / (4 : ℚ) ^ (m + 1)) *
            ((Nat.centralBinom (m + 1 - (m + 1)) : ℚ) / (4 : ℚ) ^ (m + 1 - (m + 1))) := by
      rw [Nat.sub_self, localFactor_zero, show 2 * m + 2 = 2 * (m + 1) by omega,
        localFactor_two_mul]
      simp
    have heven :
        ∑ i ∈ Finset.range (m + 1), localFactor (2 * i) * localFactor (2 * m + 2 - 2 * i) +
            localFactor (2 * m + 2) * localFactor (2 * m + 2 - (2 * m + 2)) = 1 := by
      have hcongr :
          ∑ i ∈ Finset.range (m + 1), localFactor (2 * i) * localFactor (2 * m + 2 - 2 * i) =
            ∑ i ∈ Finset.range (m + 1),
              ((Nat.centralBinom i : ℚ) / (4 : ℚ) ^ i) *
                ((Nat.centralBinom (m + 1 - i) : ℚ) / (4 : ℚ) ^ (m + 1 - i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hle : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [localFactor_two_mul, show 2 * m + 2 - 2 * i = 2 * (m + 1 - i) by omega,
          localFactor_two_mul]
      rw [hcongr, htop, ← Finset.sum_range_succ
        (fun i => ((Nat.centralBinom i : ℚ) / (4 : ℚ) ^ i) *
          ((Nat.centralBinom (m + 1 - i) : ℚ) / (4 : ℚ) ^ (m + 1 - i))) (m + 1)]
      exact centralBinom_conv_rat (m + 1)
    have hodd :
        ∑ i ∈ Finset.range (m + 1),
            localFactor (2 * i + 1) * localFactor (2 * m + 2 - (2 * i + 1)) = 1 := by
      have hcongr :
          ∑ i ∈ Finset.range (m + 1),
              localFactor (2 * i + 1) * localFactor (2 * m + 2 - (2 * i + 1)) =
            ∑ i ∈ Finset.range (m + 1),
              ((Nat.centralBinom i : ℚ) / (4 : ℚ) ^ i) *
                ((Nat.centralBinom (m - i) : ℚ) / (4 : ℚ) ^ (m - i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hle : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [localFactor_two_mul_add_one,
          show 2 * m + 2 - (2 * i + 1) = 2 * (m - i) + 1 by omega,
          localFactor_two_mul_add_one]
      rw [hcongr]
      exact centralBinom_conv_rat m
    linarith
  · -- Case `e = 2 * m + 1`
    rw [show 2 * m + 1 + 1 = 2 * m + 2 by omega, sum_range_pair]
    have hcongr :
        ∑ i ∈ Finset.range (m + 1),
            (localFactor (2 * i) * localFactor (2 * m + 1 - 2 * i) +
              localFactor (2 * i + 1) * localFactor (2 * m + 1 - (2 * i + 1))) =
          2 * ∑ i ∈ Finset.range (m + 1),
            ((Nat.centralBinom i : ℚ) / (4 : ℚ) ^ i) *
              ((Nat.centralBinom (m - i) : ℚ) / (4 : ℚ) ^ (m - i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hle : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [localFactor_two_mul, show 2 * m + 1 - 2 * i = 2 * (m - i) + 1 by omega,
        localFactor_two_mul_add_one, localFactor_two_mul_add_one,
        show 2 * m + 1 - (2 * i + 1) = 2 * (m - i) by omega, localFactor_two_mul]
      ring
    rw [hcongr, centralBinom_conv_rat m, mul_one]

theorem g_mul_self_eq_u : g * g = u := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    (g * g) (g_isMultiplicative.mul g_isMultiplicative) u u_isMultiplicative]
  intro p e hp
  rcases eq_or_ne e 0 with rfl | he
  · simp [(g_isMultiplicative.mul g_isMultiplicative).1, u_isMultiplicative.1]
  · rw [u_prime_pow_pos hp he, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun x y => g x * g y), Nat.sum_divisors_prime_pow hp]
    have hcongr :
        ∑ j ∈ Finset.range (e + 1), g (p ^ j) * g (p ^ e / p ^ j) =
          ∑ j ∈ Finset.range (e + 1), localFactor j * localFactor (e - j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hle : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Nat.pow_div hle hp.pos, g_prime_pow hp j, g_prime_pow hp (e - j)]
    rw [hcongr, localFactor_conv_eq_two he]

theorem f_spec : f 1 = 1 ∧ f * f = u := by
  classical
  have hex : ∃ h : ArithmeticFunction ℚ, h 1 = 1 ∧ h * h = u := ⟨g, g_one, g_mul_self_eq_u⟩
  have hf_def : f = Classical.choose hex := by simp only [f, hex, ↓reduceDIte]
  rw [hf_def]
  exact Classical.choose_spec hex

theorem g_eq_f : g = f :=
  dirichlet_sqrt_unique ⟨g_one, g_mul_self_eq_u⟩ f_spec

/-! ### Step D3: Legendre/Kummer 2-adic Valuation of `B_m` and Oddness of `A001790` -/

abbrev s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

theorem s2_le (n : ℕ) : s2 n ≤ n :=
  Nat.digit_sum_le 2 n

theorem s2_two_mul (m : ℕ) : s2 (2 * m) = s2 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · rw [s2, Nat.digits_base_mul (by decide) hm, List.sum_cons, zero_add]

theorem fact_two_add_s2 (n : ℕ) : n.factorial.factorization 2 + s2 n = n := by
  have hleg := Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
  have hle := s2_le n
  dsimp [s2] at hle ⊢
  omega

theorem centralBinom_factorization_two (m : ℕ) :
    (Nat.centralBinom m).factorization 2 = s2 m := by
  have hchoose : Nat.centralBinom m * m.factorial * m.factorial = (2 * m).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left m (by decide : 0 < 2))
    rwa [show 2 * m - m = m by omega] at h
  have hcb_ne : Nat.centralBinom m ≠ 0 := (Nat.centralBinom_pos m).ne'
  have hm_ne : m.factorial ≠ 0 := Nat.factorial_ne_zero m
  have hf := congrArg (fun x : ℕ => x.factorization 2) hchoose
  rw [Nat.factorization_mul (mul_ne_zero hcb_ne hm_ne) hm_ne,
    Nat.factorization_mul hcb_ne hm_ne, Finsupp.add_apply, Finsupp.add_apply] at hf
  have h1 := fact_two_add_s2 m
  have h2 := fact_two_add_s2 (2 * m)
  have h3 := s2_two_mul m
  omega

theorem two_pow_s2_dvd_centralBinom (m : ℕ) : 2 ^ s2 m ∣ Nat.centralBinom m := by
  rw [Nat.prime_two.pow_dvd_iff_le_factorization (Nat.centralBinom_pos m).ne',
    centralBinom_factorization_two]

theorem two_pow_s2_mul_A001790 (m : ℕ) : 2 ^ s2 m * A001790 m = Nat.centralBinom m :=
  Nat.mul_div_cancel' (two_pow_s2_dvd_centralBinom m)

theorem A001790_pos (m : ℕ) : 0 < A001790 m := by
  rcases Nat.eq_zero_or_pos (A001790 m) with h0 | hpos
  · exfalso
    have hcb := two_pow_s2_mul_A001790 m
    rw [h0, mul_zero] at hcb
    exact (Nat.centralBinom_pos m).ne' hcb.symm
  · exact hpos

theorem A001790_factorization_two (m : ℕ) : (A001790 m).factorization 2 = 0 := by
  have hmul := congrArg (fun x : ℕ => x.factorization 2) (two_pow_s2_mul_A001790 m)
  rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) (A001790_pos m).ne',
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    centralBinom_factorization_two] at hmul
  omega

theorem A001790_coprime_two (m : ℕ) : Nat.Coprime (A001790 m) 2 := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two,
    Nat.prime_two.dvd_iff_one_le_factorization (A001790_pos m).ne', A001790_factorization_two]
  omega

theorem A001790_odd (m : ℕ) : Odd (A001790 m) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro hdvd
  have hcop := A001790_coprime_two m
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at hcop
  exact hcop hdvd

/-! ### Step D4: `Rat.num` No-Cancellation Bridge & Eldar's Prime-Power Formula -/

theorem localFactor_eq_A001790_div (e : ℕ) :
    localFactor e = (A001790 (e / 2) : ℚ) / (2 : ℚ) ^ (2 * (e / 2) - s2 (e / 2)) := by
  set m := e / 2
  have hs : s2 m ≤ 2 * m := (s2_le m).trans (by omega)
  have hpow : (4 : ℚ) ^ m = (2 : ℚ) ^ s2 m * (2 : ℚ) ^ (2 * m - s2 m) := by
    rw [← pow_add, show s2 m + (2 * m - s2 m) = 2 * m by omega, pow_mul]
    norm_num
  have hcb : (Nat.centralBinom m : ℚ) = (2 : ℚ) ^ s2 m * (A001790 m : ℚ) := by
    exact_mod_cast (two_pow_s2_mul_A001790 m).symm
  rw [localFactor, hcb, hpow, mul_div_mul_left _ _ (by positivity)]

theorem num_nat_div_two_pow {N : ℕ} (hcop : Nat.Coprime N 2) (d : ℕ) :
    ((N : ℚ) / (2 : ℚ) ^ d).num = (N : ℤ) := by
  have hq : ((N : ℚ) / (2 : ℚ) ^ d) = ((N : ℤ) : ℚ) / ((2 ^ d : ℕ) : ℤ) := by push_cast; rfl
  rw [hq]
  refine Rat.num_div_eq_of_coprime (by positivity) ?_
  simp only [Int.natAbs_natCast]
  exact hcop.pow_right d

theorem a_eq_prod_A001790 {n : ℕ} (hn : n ≠ 0) :
    a n = ((∏ p ∈ n.primeFactors, A001790 (n.factorization p / 2) : ℕ) : ℤ) := by
  rw [a, ← g_eq_f, g_apply_of_ne_zero hn]
  have hprod :
      ∏ p ∈ n.primeFactors, localFactor (n.factorization p) =
        ((∏ p ∈ n.primeFactors, A001790 (n.factorization p / 2) : ℕ) : ℚ) /
          (2 : ℚ) ^ (∑ p ∈ n.primeFactors,
            (2 * (n.factorization p / 2) - s2 (n.factorization p / 2))) := by
    simp_rw [localFactor_eq_A001790_div]
    rw [Finset.prod_div_distrib, Nat.cast_prod, Finset.prod_pow_eq_pow_sum]
  rw [hprod]
  refine num_nat_div_two_pow ?_ _
  exact Nat.Coprime.prod_left fun p _ => A001790_coprime_two _

/-- Amiram Eldar's `Nov 01 2026` `%F` formula on `OEIS A317933`, proved from first principles. -/
theorem a_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    a (p ^ e) = (A001790 (e / 2) : ℤ) := by
  rw [a, ← g_eq_f, g_prime_pow hp e, localFactor_eq_A001790_div]
  exact num_nat_div_two_pow (A001790_coprime_two _) _

/-! ### Steps D5 & D6: Digit-Sum Subadditivity, Monotonicity, and Supermultiplicativity -/

theorem s2_add_le (x y : ℕ) : s2 (x + y) ≤ s2 x + s2 y := by
  have hchoose : (x + y).choose x * x.factorial * y.factorial = (x + y).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right x y)
    rwa [Nat.add_sub_cancel_left] at h
  have hc_ne : (x + y).choose x ≠ 0 := (Nat.choose_pos (Nat.le_add_right x y)).ne'
  have hx_ne : x.factorial ≠ 0 := Nat.factorial_ne_zero x
  have hy_ne : y.factorial ≠ 0 := Nat.factorial_ne_zero y
  have hf := congrArg (fun z : ℕ => z.factorization 2) hchoose
  rw [Nat.factorization_mul (mul_ne_zero hc_ne hx_ne) hy_ne,
    Nat.factorization_mul hc_ne hx_ne, Finsupp.add_apply, Finsupp.add_apply] at hf
  have h1 := fact_two_add_s2 x
  have h2 := fact_two_add_s2 y
  have h3 := fact_two_add_s2 (x + y)
  omega

theorem A001790_strictMono_from_one {k : ℕ} (hk : 1 ≤ k) : A001790 k < A001790 (k + 1) := by
  have hrec := Nat.succ_mul_centralBinom_succ k
  rw [← two_pow_s2_mul_A001790 (k + 1), ← two_pow_s2_mul_A001790 k] at hrec
  have hs : s2 (k + 1) ≤ s2 k + 1 := by
    have h := s2_add_le k 1
    have hs1 : s2 1 = 1 := by decide
    omega
  have hpow : 2 ^ s2 (k + 1) ≤ 2 * 2 ^ s2 k := by
    calc
      2 ^ s2 (k + 1) ≤ 2 ^ (s2 k + 1) := Nat.pow_le_pow_right (by decide) hs
      _ = 2 * 2 ^ s2 k := by rw [pow_succ']
  have hpos_g : 0 < A001790 k := A001790_pos k
  have hpos_p : 0 < 2 ^ s2 (k + 1) := by positivity
  have hlt1 :
      ((k + 1) * 2 ^ s2 (k + 1)) * A001790 k < ((2 * k + 1) * 2 ^ s2 (k + 1)) * A001790 k := by
    have hlt_factor : (k + 1) * 2 ^ s2 (k + 1) < (2 * k + 1) * 2 ^ s2 (k + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) hpos_p
    exact Nat.mul_lt_mul_of_pos_right hlt_factor hpos_g
  have hle2 :
      ((2 * k + 1) * 2 ^ s2 (k + 1)) * A001790 k ≤
        ((k + 1) * 2 ^ s2 (k + 1)) * A001790 (k + 1) := by
    have hmul : (2 * k + 1) * 2 ^ s2 (k + 1) ≤ (2 * k + 1) * (2 * 2 ^ s2 k) :=
      Nat.mul_le_mul_left _ hpow
    have hmul2 :
        ((2 * k + 1) * 2 ^ s2 (k + 1)) * A001790 k ≤
          ((2 * k + 1) * (2 * 2 ^ s2 k)) * A001790 k :=
      Nat.mul_le_mul_right _ hmul
    have hrhs :
        ((2 * k + 1) * (2 * 2 ^ s2 k)) * A001790 k =
          ((k + 1) * 2 ^ s2 (k + 1)) * A001790 (k + 1) := by
      calc
        ((2 * k + 1) * (2 * 2 ^ s2 k)) * A001790 k
          = 2 * (2 * k + 1) * (2 ^ s2 k * A001790 k) := by ring
        _ = (k + 1) * (2 ^ s2 (k + 1) * A001790 (k + 1)) := hrec.symm
        _ = ((k + 1) * 2 ^ s2 (k + 1)) * A001790 (k + 1) := by ring
    rwa [hrhs] at hmul2
  exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hlt1 hle2)

theorem A001790_mono : Monotone A001790 := by
  refine monotone_nat_of_le_succ fun k => ?_
  rcases k with _ | k
  · decide
  · exact (A001790_strictMono_from_one (Nat.succ_pos k)).le

theorem A001790_lt_of_lt {j k : ℕ} (hk : 2 ≤ k) (hjk : j < k) : A001790 j < A001790 k := by
  have hjle : j ≤ k - 1 := by omega
  have hk1 : 1 ≤ k - 1 := by omega
  calc
    A001790 j ≤ A001790 (k - 1) := A001790_mono hjle
    _ < A001790 (k - 1 + 1) := A001790_strictMono_from_one hk1
    _ = A001790 k := by rw [Nat.sub_add_cancel (by omega)]

theorem centralBinom_supermult (x y : ℕ) :
    Nat.centralBinom x * Nat.centralBinom y ≤ Nat.centralBinom (x + y) := by
  change (2 * x).choose x * (2 * y).choose y ≤ (2 * (x + y)).choose (x + y)
  rw [Nat.mul_add, Nat.add_choose_eq]
  have hmem : (x, y) ∈ Finset.antidiagonal (x + y) := Finset.mem_antidiagonal.mpr rfl
  exact Finset.single_le_sum
    (f := fun ij : ℕ × ℕ => (2 * x).choose ij.1 * (2 * y).choose ij.2)
    (fun _ _ => Nat.zero_le _) hmem

theorem A001790_supermult (x y : ℕ) : A001790 x * A001790 y ≤ A001790 (x + y) := by
  have hpow : 2 ^ s2 (x + y) ≤ 2 ^ (s2 x + s2 y) :=
    Nat.pow_le_pow_right (by decide) (s2_add_le x y)
  have hineq :
      2 ^ (s2 x + s2 y) * (A001790 x * A001790 y) ≤
        2 ^ (s2 x + s2 y) * A001790 (x + y) := by
    calc
      2 ^ (s2 x + s2 y) * (A001790 x * A001790 y)
        = (2 ^ s2 x * A001790 x) * (2 ^ s2 y * A001790 y) := by rw [pow_add]; ring
      _ = Nat.centralBinom x * Nat.centralBinom y := by
          rw [two_pow_s2_mul_A001790, two_pow_s2_mul_A001790]
      _ ≤ Nat.centralBinom (x + y) := centralBinom_supermult x y
      _ = 2 ^ s2 (x + y) * A001790 (x + y) := (two_pow_s2_mul_A001790 (x + y)).symm
      _ ≤ 2 ^ (s2 x + s2 y) * A001790 (x + y) := Nat.mul_le_mul_right _ hpow
  exact Nat.le_of_mul_le_mul_left hineq (by positivity)

theorem prod_A001790_le {ι : Type*} (s : Finset ι) (w : ι → ℕ) :
    ∏ i ∈ s, A001790 (w i) ≤ A001790 (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [A001790]
  | insert x t hxt ih =>
    rw [Finset.prod_insert hxt, Finset.sum_insert hxt]
    exact (Nat.mul_le_mul_left _ ih).trans (A001790_supermult (w x) _)

/-- Refutation witness for Trap #1 (`SCOPING-C047.md` §2.1): at `k = 31, m₁ = 29, m₂ = 1`,
`4 ^ 29 * 9 ^ 1 < 4 ^ 31`, yet `(C(58, 29) / 2) * A001790 1 > A001790 31`. -/
theorem triage_step2_bound_false_at_31 :
    4 ^ 29 * 9 ^ 1 < 4 ^ 31 ∧ ¬ ((Nat.choose (2 * 29) 29 / 2) * A001790 1 < A001790 31) := by
  decide

/-! ### Steps D7 & D8: Exponent-Sum Dominance `4 ^ M(n) ≤ n` and Record Characterization -/

def M (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, n.factorization p / 2

theorem prod_le_prod_nat {ι : Type*} (s : Finset ι) {f₁ f₂ : ι → ℕ}
    (h : ∀ i ∈ s, f₁ i ≤ f₂ i) : ∏ i ∈ s, f₁ i ≤ ∏ i ∈ s, f₂ i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x t hxt ih =>
    rw [Finset.prod_insert hxt, Finset.prod_insert hxt]
    exact Nat.mul_le_mul (h x (Finset.mem_insert_self x t))
      (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

theorem four_pow_M_le {n : ℕ} (hn : n ≠ 0) : 4 ^ M n ≤ n := by
  have hn_eq : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors (· ^ ·),
      Nat.prod_factorization_pow_eq_self hn]
  nth_rw 2 [← hn_eq]
  rw [M, ← Finset.prod_pow_eq_pow_sum]
  refine prod_le_prod_nat n.primeFactors fun p hp => ?_
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : 4 ≤ p ^ 2 := by
    have h2 : 2 ≤ p := hprime.two_le
    nlinarith
  calc
    4 ^ (n.factorization p / 2)
      ≤ (p ^ 2) ^ (n.factorization p / 2) := Nat.pow_le_pow_left hp2 _
    _ = p ^ (2 * (n.factorization p / 2)) := (pow_mul p 2 _).symm
    _ ≤ p ^ n.factorization p := Nat.pow_le_pow_right hprime.pos (Nat.mul_div_le _ 2)

theorem M_four_pow (k : ℕ) : M (4 ^ k) = k := by
  have h4 : 4 ^ k = 2 ^ (2 * k) := by
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
  rw [M, h4]
  change (2 ^ (2 * k)).factorization.sum (fun _ e => e / 2) = k
  rw [Nat.prime_two.factorization_pow, Finsupp.sum_single_index (by simp)]
  omega

theorem four_pow_M_eq_self_iff {n : ℕ} (hn : n ≠ 0) :
    4 ^ M n = n ↔ ∃ k : ℕ, n = 4 ^ k := by
  constructor
  · intro h
    exact ⟨M n, h.symm⟩
  · rintro ⟨k, rfl⟩
    rw [M_four_pow]

theorem a_le_A001790_M {n : ℕ} (hn : n ≠ 0) : a n ≤ (A001790 (M n) : ℤ) := by
  rw [a_eq_prod_A001790 hn]
  exact Int.ofNat_le.mpr (prod_A001790_le n.primeFactors (fun p => n.factorization p / 2))

theorem one_le_a {n : ℕ} (hn : n ≠ 0) : (1 : ℤ) ≤ a n := by
  rw [a_eq_prod_A001790 hn]
  have h1 : 1 ≤ ∏ p ∈ n.primeFactors, A001790 (n.factorization p / 2) := by
    calc
      1 = ∏ _p ∈ n.primeFactors, 1 := (Finset.prod_const_one).symm
      _ ≤ ∏ p ∈ n.primeFactors, A001790 (n.factorization p / 2) :=
        prod_le_prod_nat n.primeFactors fun p _ => A001790_pos _
  exact_mod_cast h1

theorem a_eq_one_of_lt_sixteen {n : ℕ} (hn1 : 1 ≤ n) (hn16 : n < 16) : a n = 1 := by
  have hn0 : n ≠ 0 := by omega
  have h4M : 4 ^ M n < 4 ^ 2 := (four_pow_M_le hn0).trans_lt (by omega)
  have hMlt : M n < 2 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 4)).mp h4M
  have hle1 : A001790 (M n) ≤ A001790 1 := A001790_mono (by omega)
  have ha1_val : A001790 1 = 1 := by decide
  have hub : a n ≤ (A001790 (M n) : ℤ) := a_le_A001790_M hn0
  have hlb : (1 : ℤ) ≤ a n := one_le_a hn0
  omega

theorem a_one_eq_A001790_zero : a 1 = (A001790 0 : ℤ) := by
  have hf1 : f 1 = 1 := f_spec.1
  have ha0 : A001790 0 = 1 := by decide
  rw [a, hf1, ha0]
  rfl

theorem a_four_pow (k : ℕ) : a (4 ^ k) = (A001790 k : ℤ) := by
  have h4 : 4 ^ k = 2 ^ (2 * k) := by
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
  rw [h4, a_prime_pow Nat.prime_two (2 * k), show 2 * k / 2 = k by omega]

/-! ### Pinned Theorem Obligations (`PIN-C047.md` v1 §2) -/

theorem f_existsUnique : (f 1 = 1 ∧ f * f = u) ∧ ∀ g : ArithmeticFunction ℚ, g 1 = 1 ∧ g * g = u → g = f := by
  exact ⟨f_spec, fun h hh => dirichlet_sqrt_unique hh f_spec⟩

theorem A001790_eq_num : ∀ k : ℕ, ((Nat.choose (2 * k) k : ℚ) / 4 ^ k).num = (A001790 k : ℤ) := by
  intro k
  have hlf : ((Nat.choose (2 * k) k : ℚ) / 4 ^ k) = localFactor (2 * k) := by
    rw [localFactor_two_mul]; rfl
  rw [hlf, localFactor_eq_A001790_div, show 2 * k / 2 = k by omega]
  exact num_nat_div_two_pow (A001790_coprime_two k) _

theorem a317933_records : (∀ n : ℕ, isStrictRecord a n ↔ (n = 1 ∨ ∃ k ≥ 2, n = 4 ^ k)) ∧ a 1 = (A001790 0 : ℤ) ∧ (∀ k ≥ 2, a (4 ^ k) = (A001790 k : ℤ)) := by
  refine ⟨?_, a_one_eq_A001790_zero, fun k _ => a_four_pow k⟩
  intro n
  constructor
  · intro hrec
    obtain ⟨hn1, hlt_all⟩ := hrec
    rcases eq_or_ne n 1 with rfl | hne1
    · exact Or.inl rfl
    have hn0 : n ≠ 0 := by omega
    rcases le_or_gt (M n) 1 with hM1 | hM2
    · exfalso
      have ha_le : a n ≤ 1 := by
        have hm : A001790 (M n) ≤ A001790 1 := A001790_mono hM1
        have ha1_val : A001790 1 = 1 := by decide
        have hle := a_le_A001790_M hn0
        omega
      have ha1 : a 1 = 1 := by
        rw [a_one_eq_A001790_zero]
        decide
      have h1lt : a 1 < a n := hlt_all 1 le_rfl (by omega)
      omega
    · rcases eq_or_ne n (4 ^ M n) with h_eq | h_ne
      · exact Or.inr ⟨M n, hM2, h_eq⟩
      · exfalso
        have h4le : 4 ^ M n ≤ n := four_pow_M_le hn0
        have h4lt : 4 ^ M n < n := lt_of_le_of_ne h4le h_ne.symm
        have h4pos : 1 ≤ 4 ^ M n := Nat.one_le_pow _ 4 (by decide)
        have hrec_4 : a (4 ^ M n) < a n := hlt_all (4 ^ M n) h4pos h4lt
        have ha4 : a (4 ^ M n) = (A001790 (M n) : ℤ) := a_four_pow (M n)
        have han : a n ≤ (A001790 (M n) : ℤ) := a_le_A001790_M hn0
        omega
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · refine ⟨le_rfl, fun m hm1 hmlt => ?_⟩
      omega
    · refine ⟨Nat.one_le_pow k 4 (by decide), fun m hm1 hmlt => ?_⟩
      have hm0 : m ≠ 0 := by omega
      have h4M : 4 ^ M m < 4 ^ k := (four_pow_M_le hm0).trans_lt hmlt
      have hMk : M m < k := (Nat.pow_lt_pow_iff_right (by decide : 1 < 4)).mp h4M
      have hA_lt : A001790 (M m) < A001790 k := A001790_lt_of_lt hk hMk
      have ham : a m ≤ (A001790 (M m) : ℤ) := a_le_A001790_M hm0
      rw [a_four_pow k]
      omega

/-! ### Computable Mirror, Kernel Spot Checks, and Guard-Sharpness Witnesses -/

/-- Computable numerator mirror via `g`, proved equal to `a` across all `n : ℕ`. -/
def a_mirror (n : ℕ) : ℤ := (g n).num

theorem a_mirror_eq_a (n : ℕ) : a_mirror n = a n := by
  rw [a_mirror, a, g_eq_f]

theorem a_spot_checks :
    a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 1 ∧ a 4 = 1 ∧ a 5 = 1 ∧
      a 16 = 3 ∧ a 64 = 5 ∧ a 256 = 35 ∧ a 1024 = 63 ∧ a 4096 = 231 := by
  have h1 : a 1 = (A001790 0 : ℤ) := a_one_eq_A001790_zero
  have h2 : a 2 = (A001790 0 : ℤ) := by simpa using a_prime_pow Nat.prime_two 1
  have h3 : a 3 = (A001790 0 : ℤ) := by simpa using a_prime_pow Nat.prime_three 1
  have h4 : a 4 = (A001790 1 : ℤ) := a_four_pow 1
  have h5 : a 5 = (A001790 0 : ℤ) := by simpa using a_prime_pow (by decide : Nat.Prime 5) 1
  have h16 : a 16 = (A001790 2 : ℤ) := a_four_pow 2
  have h64 : a 64 = (A001790 3 : ℤ) := a_four_pow 3
  have h256 : a 256 = (A001790 4 : ℤ) := a_four_pow 4
  have h1024 : a 1024 = (A001790 5 : ℤ) := a_four_pow 5
  have h4096 : a 4096 = (A001790 6 : ℤ) := a_four_pow 6
  rw [h1, h2, h3, h4, h5, h16, h64, h256, h1024, h4096]
  decide

theorem guard_exclusions :
    ¬ isStrictRecord a 0 ∧
      ¬ isStrictRecord a 2 ∧
      ¬ isStrictRecord a 3 ∧
      ¬ isStrictRecord a 4 ∧
      ¬ isStrictRecord a 5 ∧
      a 4 = a 1 := by
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := a_spot_checks
  refine ⟨?_, ?_, ?_, ?_, ?_, by omega⟩
  · intro h; exact absurd h.1 (by decide)
  · intro h; have := h.2 1 le_rfl (by decide); omega
  · intro h; have := h.2 1 le_rfl (by decide); omega
  · intro h; have := h.2 1 le_rfl (by decide); omega
  · intro h; have := h.2 1 le_rfl (by decide); omega

end Mathproofs.A317933Records
