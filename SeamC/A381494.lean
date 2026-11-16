import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Seam C `S019` (`OEIS A381494 = A218358`): Base-7 Reciprocal Period and `GF(7)` Irreducible Order

Formalizes and proves R. J. Mathar's Mar 03 2025 conjecture on `OEIS A381494` (`%F` line 14,
live revision `#23 Mar 02 2026 13:15:08`) and companion `OEIS A218358` (`%N` line 10, `%F` line 15,
live revision `#17 Feb 16 2025 08:33:18`) against the frozen contract `PIN-S019.md` v1
(`delta_vs_source: NONE`), following the five-step primitive-divisor bridge (`Steps 1–5`) from
`SCOPING-S019.md` §2.1 directly between the two primary `%N` definitions.
-/

namespace SeamC.A381494

/-! ### Frozen Target Definitions (`PIN-S019.md` v1) -/

/-- `k`-th base-7 digit after the radix point (`k ≥ 1`) of `1 / m` (`PIN-S019.md` v1;
matching `OEIS A381494` `%e`: for `m = 9`, `k = 1..6` yields `0, 5, 3, 0, 5, 3`). -/
def base7RecipDigit (m k : ℕ) : ℕ :=
  (7 ^ k / m) % 7

/-- `OEIS A381494` period-length predicate (`PIN-S019.md` v1): holds iff `1 ≤ m` and
(a) for `n = 0`, the base-7 expansion terminates (`∃ K ≥ 1, ∀ k ≥ K, base7RecipDigit m k = 0`),
while (b) for `n ≥ 1`, the base-7 expansion does not terminate, admits `n` as an eventual period,
and admits no smaller positive eventual period. -/
def HasBase7RecipPeriodLen (m n : ℕ) : Prop :=
  1 ≤ m ∧
    ((n = 0 ∧ ∃ K ≥ 1, ∀ k ≥ K, base7RecipDigit m k = 0) ∨
      (1 ≤ n ∧
        (¬ ∃ K ≥ 1, ∀ k ≥ K, base7RecipDigit m k = 0) ∧
        (∃ K ≥ 1, ∀ k ≥ K, base7RecipDigit m (k + n) = base7RecipDigit m k) ∧
        (∀ p : ℕ, 1 ≤ p → p < n →
          ¬ ∃ K ≥ 1, ∀ k ≥ K, base7RecipDigit m (k + p) = base7RecipDigit m k)))

/-- `OEIS A381494(n)` (`%N` line 10; `PIN-S019.md` v1): smallest positive integer `m` whose
reciprocal `1 / m` has period length `n` in base 7. -/
noncomputable def base7LeastPeriodDenominator (n : ℕ) : ℕ :=
  sInf { m : ℕ | HasBase7RecipPeriodLen m n }

/-- Polynomial order over `GF(7)` (Lidl & Niederreiter Def. 3.2; `PIN-S019.md` v1): least
positive integer `e` such that `f(X)` divides `X^e - 1` in `(ZMod 7)[X]`. -/
noncomputable def polyOrder (f : Polynomial (ZMod 7)) : ℕ :=
  sInf { e : ℕ | 1 ≤ e ∧ f ∣ (Polynomial.X ^ e - 1) }

/-- `OEIS A218358(n)` (`%N` line 10; `PIN-S019.md` v1): minimal polynomial order among monic
degree-`n` irreducible polynomials over `GF(7)` with nonzero constant term. -/
noncomputable def minIrredOrder (n : ℕ) : ℕ :=
  sInf { d : ℕ | ∃ f : Polynomial (ZMod 7),
    f.Monic ∧ Irreducible f ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 ∧ d = polyOrder f }

/-! ### Step 1: Primitive Divisors `S(n)` of `7^n - 1` (`SCOPING-S019.md` §2.1 Step 1) -/

local instance instFactPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private lemma nat_sInf_eq_of_mem_of_le {S : Set ℕ} {m₀ : ℕ}
    (hm₀ : m₀ ∈ S) (hle : ∀ m ∈ S, m₀ ≤ m) : sInf S = m₀ :=
  le_antisymm (Nat.sInf_le hm₀) (hle _ (Nat.sInf_mem ⟨m₀, hm₀⟩))

/-- Internal bridge predicate `S(n)`: primitive divisors `d > 1` of `7^n - 1` dividing no
`7^k - 1` for `1 ≤ k < n`. -/
private def IsPrimitiveDivisor7 (n d : ℕ) : Prop :=
  1 < d ∧ d ∣ (7 ^ n - 1) ∧ ∀ k : ℕ, 1 ≤ k → k < n → ¬ d ∣ (7 ^ k - 1)

private noncomputable def minPrimDiv7 (n : ℕ) : ℕ :=
  sInf { d : ℕ | IsPrimitiveDivisor7 n d }

private lemma seven_pow_pos (k : ℕ) : 0 < 7 ^ k :=
  Nat.pow_pos (by decide)

private lemma one_lt_seven_pow {k : ℕ} (hk : 1 ≤ k) : 1 < 7 ^ k :=
  Nat.one_lt_pow (by omega) (by decide)

/-- Step 1 (`SCOPING-S019.md` §2.1): for `n ≥ 1`, `7^n - 1 ∈ S(n)`, so `S(n)` is nonempty. -/
private lemma self_mem_primitiveDivisors7 {n : ℕ} (hn : 1 ≤ n) :
    IsPrimitiveDivisor7 n (7 ^ n - 1) := by
  have hgt : 1 < 7 ^ n := one_lt_seven_pow hn
  have hge7 : 7 ≤ 7 ^ n := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 7) hn
  refine ⟨by omega, dvd_rfl, ?_⟩
  intro k hk1 hkn hdvd
  have hk_gt : 1 < 7 ^ k := one_lt_seven_pow hk1
  have hpow_lt : 7 ^ k < 7 ^ n := Nat.pow_lt_pow_right (by decide : 1 < 7) hkn
  have hle : 7 ^ n - 1 ≤ 7 ^ k - 1 := Nat.le_of_dvd (by omega) hdvd
  omega

private lemma minPrimDiv7_mem {n : ℕ} (hn : 1 ≤ n) :
    IsPrimitiveDivisor7 n (minPrimDiv7 n) :=
  Nat.sInf_mem (s := { d : ℕ | IsPrimitiveDivisor7 n d })
    ⟨7 ^ n - 1, self_mem_primitiveDivisors7 hn⟩

private lemma minPrimDiv7_le {n d : ℕ} (hd : IsPrimitiveDivisor7 n d) :
    minPrimDiv7 n ≤ d :=
  Nat.sInf_le hd

private lemma coprime_seven_of_dvd_seven_pow_sub_one {n d : ℕ} (hn : 1 ≤ n)
    (hd : d ∣ 7 ^ n - 1) : Nat.Coprime d 7 := by
  rw [Nat.Coprime, Nat.gcd_comm]
  refine (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr ?_
  intro h7d
  have h7sub : 7 ∣ 7 ^ n - 1 := dvd_trans h7d hd
  have h7pow : 7 ∣ 7 ^ n := dvd_pow_self 7 (by omega : n ≠ 0)
  have hpos : 1 ≤ 7 ^ n := Nat.le_of_lt (one_lt_seven_pow hn)
  rcases h7sub with ⟨a, ha⟩
  rcases h7pow with ⟨b, hb⟩
  omega

/-! ### Step 2: Discrete Base-7 Reciprocal Period Bridge (`SCOPING-S019.md` §2.1 Step 2) -/

private def Base7Terminates (m : ℕ) : Prop :=
  ∃ K ≥ 1, ∀ k ≥ K, base7RecipDigit m k = 0

private def Base7EventualPeriod (m p : ℕ) : Prop :=
  ∃ K ≥ 1, ∀ k ≥ K, base7RecipDigit m (k + p) = base7RecipDigit m k

/-- Multiplying `m` by `7^v` shifts all post-radix digits by `v` places. -/
private lemma base7RecipDigit_seven_pow_mul (v m' j : ℕ) :
    base7RecipDigit (7 ^ v * m') (v + j) = base7RecipDigit m' j := by
  unfold base7RecipDigit
  rw [pow_add, Nat.mul_div_mul_left _ _ (seven_pow_pos v)]

private lemma terminates_seven_pow_mul_iff (v m' : ℕ) :
    Base7Terminates (7 ^ v * m') ↔ Base7Terminates m' := by
  constructor
  · rintro ⟨K, hK1, hK⟩
    refine ⟨K, hK1, fun j hj => ?_⟩
    rw [← base7RecipDigit_seven_pow_mul v m' j]
    exact hK (v + j) (by omega)
  · rintro ⟨K, hK1, hK⟩
    refine ⟨v + K, by omega, fun k hk => ?_⟩
    rw [show k = v + (k - v) by omega, base7RecipDigit_seven_pow_mul]
    exact hK (k - v) (by omega)

private lemma eventualPeriod_seven_pow_mul_iff (v m' p : ℕ) :
    Base7EventualPeriod (7 ^ v * m') p ↔ Base7EventualPeriod m' p := by
  constructor
  · rintro ⟨K, hK1, hK⟩
    refine ⟨K, hK1, fun j hj => ?_⟩
    rw [← base7RecipDigit_seven_pow_mul v m' (j + p),
      ← base7RecipDigit_seven_pow_mul v m' j,
      show v + (j + p) = (v + j) + p by omega]
    exact hK (v + j) (by omega)
  · rintro ⟨K, hK1, hK⟩
    refine ⟨v + K, by omega, fun k hk => ?_⟩
    rw [show k + p = v + (k - v + p) by omega, base7RecipDigit_seven_pow_mul,
      hK (k - v) (by omega), ← base7RecipDigit_seven_pow_mul v m' (k - v),
      show v + (k - v) = k by omega]

private lemma hasBase7RecipPeriodLen_seven_pow_mul_iff {m' : ℕ} (hm' : 1 ≤ m') (v n : ℕ) :
    HasBase7RecipPeriodLen (7 ^ v * m') n ↔ HasBase7RecipPeriodLen m' n := by
  have hm_ge : 1 ≤ 7 ^ v * m' := Nat.mul_pos (seven_pow_pos v) hm'
  change (1 ≤ 7 ^ v * m' ∧
      ((n = 0 ∧ Base7Terminates (7 ^ v * m')) ∨
        (1 ≤ n ∧ ¬ Base7Terminates (7 ^ v * m') ∧ Base7EventualPeriod (7 ^ v * m') n ∧
          ∀ p : ℕ, 1 ≤ p → p < n → ¬ Base7EventualPeriod (7 ^ v * m') p))) ↔
    (1 ≤ m' ∧
      ((n = 0 ∧ Base7Terminates m') ∨
        (1 ≤ n ∧ ¬ Base7Terminates m' ∧ Base7EventualPeriod m' n ∧
          ∀ p : ℕ, 1 ≤ p → p < n → ¬ Base7EventualPeriod m' p)))
  simp only [hm_ge, hm', true_and, terminates_seven_pow_mul_iff, eventualPeriod_seven_pow_mul_iff]

/-- Every positive integer factors as `7^v * m'` with `1 ≤ m'` and `Nat.Coprime m' 7`. -/
private lemma exists_seven_pow_mul_coprime :
    ∀ {m : ℕ}, 1 ≤ m → ∃ v m' : ℕ, m = 7 ^ v * m' ∧ 1 ≤ m' ∧ Nat.Coprime m' 7 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases h7 : 7 ∣ m
    · rcases h7 with ⟨k, rfl⟩
      have hk1 : 1 ≤ k := by omega
      have hk_lt : k < 7 * k := by omega
      obtain ⟨v, m', rfl, hm'1, hcop⟩ := ih k hk_lt hk1
      refine ⟨v + 1, m', ?_, hm'1, hcop⟩
      rw [pow_succ']
      ring
    · refine ⟨0, m, by simp, hm, ?_⟩
      rw [Nat.Coprime, Nat.gcd_comm]
      exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr h7

/-- Exact quotient step `⌊7^(k+1)/m⌋ = 7 * ⌊7^k/m⌋ + d_{k+1}(m)`. -/
private lemma seven_pow_div_step (m k : ℕ) :
    7 ^ (k + 1) / m = 7 * (7 ^ k / m) + base7RecipDigit m (k + 1) := by
  set Q := 7 ^ (k + 1) / m
  have hdiv : Q / 7 = 7 ^ k / m := by
    dsimp [Q]
    rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_div_mul_right _ _ (by decide : 0 < 7)]
  have hmod : Q % 7 = base7RecipDigit m (k + 1) := rfl
  have h := (Nat.div_add_mod Q 7).symm
  rwa [hdiv, hmod] at h

/-- `P`-digit base-7 block starting after index `K`. -/
private def digitBlock (m K : ℕ) : ℕ → ℕ
  | 0 => 0
  | P + 1 => 7 * digitBlock m K P + base7RecipDigit m (K + P + 1)

private lemma digitBlock_div_eq (m K : ℕ) :
    ∀ P : ℕ, 7 ^ (K + P) / m = 7 ^ P * (7 ^ K / m) + digitBlock m K P
  | 0 => by simp [digitBlock]
  | P + 1 => by
    rw [show K + (P + 1) = (K + P) + 1 by omega, seven_pow_div_step,
      digitBlock_div_eq m K P, digitBlock, pow_succ']
    ring

private lemma digitBlock_lt_pow (m K : ℕ) :
    ∀ P : ℕ, digitBlock m K P < 7 ^ P
  | 0 => by simp [digitBlock]
  | P + 1 => by
    have ih := digitBlock_lt_pow m K P
    have hd : base7RecipDigit m (K + P + 1) < 7 := Nat.mod_lt _ (by decide)
    rw [digitBlock, pow_succ]
    omega

/-- Fundamental subtraction-free remainder-block identity:
`7^P * (7^K % m) = m * B_K + (7^(K+P) % m)`. -/
private lemma rem_block_identity (m K P : ℕ) :
    7 ^ P * (7 ^ K % m) = m * digitBlock m K P + 7 ^ (K + P) % m := by
  have h1 : m * (7 ^ (K + P) / m) + 7 ^ (K + P) % m = 7 ^ (K + P) :=
    Nat.div_add_mod (7 ^ (K + P)) m
  have h2 : m * (7 ^ K / m) + 7 ^ K % m = 7 ^ K :=
    Nat.div_add_mod (7 ^ K) m
  rw [digitBlock_div_eq] at h1
  have hcomb : m * (7 ^ P * (7 ^ K / m)) + 7 ^ P * (7 ^ K % m) =
      m * (7 ^ P * (7 ^ K / m)) + (m * digitBlock m K P + 7 ^ (K + P) % m) := by
    calc
      m * (7 ^ P * (7 ^ K / m)) + 7 ^ P * (7 ^ K % m)
          = 7 ^ P * (m * (7 ^ K / m) + 7 ^ K % m) := by ring
      _ = 7 ^ P * 7 ^ K := by rw [h2]
      _ = 7 ^ (K + P) := by rw [add_comm K P, pow_add]
      _ = m * (7 ^ P * (7 ^ K / m) + digitBlock m K P) + 7 ^ (K + P) % m := h1.symm
      _ = m * (7 ^ P * (7 ^ K / m)) + (m * digitBlock m K P + 7 ^ (K + P) % m) := by ring
  exact Nat.add_left_cancel hcomb

private lemma digitBlock_eq_zero_of_all_zero {m K : ℕ}
    (h : ∀ k : ℕ, K + 1 ≤ k → base7RecipDigit m k = 0) :
    ∀ P : ℕ, digitBlock m K P = 0
  | 0 => rfl
  | P + 1 => by
    rw [digitBlock, digitBlock_eq_zero_of_all_zero h P, h (K + P + 1) (by omega)]

private lemma digitBlock_congr {m K₁ K₂ : ℕ} :
    ∀ {P : ℕ}, (∀ t : ℕ, 1 ≤ t → t ≤ P → base7RecipDigit m (K₁ + t) = base7RecipDigit m (K₂ + t)) →
      digitBlock m K₁ P = digitBlock m K₂ P
  | 0, _ => rfl
  | P + 1, h => by
    have ih := digitBlock_congr (P := P) (fun t ht1 htle => h t ht1 (by omega))
    have hlast := h (P + 1) (by omega) le_rfl
    rw [digitBlock, digitBlock, ih,
      show K₁ + P + 1 = K₁ + (P + 1) by omega,
      show K₂ + P + 1 = K₂ + (P + 1) by omega, hlast]

private lemma terminates_one : Base7Terminates 1 := by
  refine ⟨1, le_rfl, fun k hk => ?_⟩
  unfold base7RecipDigit
  rw [Nat.div_one, show k = (k - 1) + 1 by omega, pow_succ]
  exact Nat.mul_mod_left _ 7

private lemma not_terminates_of_gt_one_coprime {m' : ℕ} (hm' : 1 < m')
    (hcop : Nat.Coprime m' 7) : ¬ Base7Terminates m' := by
  rintro ⟨K, hK1, hK⟩
  have hB0 : digitBlock m' K m' = 0 :=
    digitBlock_eq_zero_of_all_zero (fun k hk => hK k (by omega)) m'
  have hrem := rem_block_identity m' K m'
  rw [hB0, mul_zero, zero_add] at hrem
  have hndvd : ¬ m' ∣ 7 ^ K := by
    intro hdvd
    have h1 : m' ∣ 1 := by
      rw [← (hcop.pow_right K).gcd_eq_one]
      exact Nat.dvd_gcd (dvd_refl m') hdvd
    exact absurd (Nat.le_of_dvd Nat.zero_lt_one h1) (by omega)
  have hr_pos : 1 ≤ 7 ^ K % m' := by
    have hne : 7 ^ K % m' ≠ 0 := fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0)
    omega
  have hlt1 : 7 ^ (K + m') % m' < m' := Nat.mod_lt _ (by omega)
  have hlt2 : m' < 7 ^ m' := Nat.lt_pow_self (by decide : 1 < 7)
  have hmul : 7 ^ m' ≤ 7 ^ m' * (7 ^ K % m') :=
    Nat.le_mul_of_pos_right (7 ^ m') hr_pos
  omega

/-- Forward period lemma: if `m' ∣ 7^P - 1` (`m' ≥ 1`), then `P` is a period of `base7RecipDigit m'`
starting immediately at `K = 1`. -/
private lemma eventualPeriod_of_dvd_seven_pow_sub_one {m' P : ℕ} (hm' : 1 ≤ m')
    (hdvd : m' ∣ 7 ^ P - 1) : Base7EventualPeriod m' P := by
  rcases hdvd with ⟨c, hc⟩
  have hpow : 7 ^ P = m' * c + 1 := by
    have hpos : 1 ≤ 7 ^ P := seven_pow_pos P
    omega
  refine ⟨1, le_rfl, fun k hk => ?_⟩
  unfold base7RecipDigit
  have hexp : 7 ^ (k + P) = 7 ^ k + (7 ^ k * c) * m' := by
    rw [pow_add, hpow]
    ring
  rw [hexp, Nat.add_mul_div_right _ _ (by omega : 0 < m')]
  have h7 : 7 ^ k * c = (7 ^ (k - 1) * c) * 7 := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  rw [h7, Nat.add_mul_mod_self_right]

/-- Converse period lemma via `ℤ` boundedness cancellation (`SCOPING-S019.md` §2.1 Step 2):
if `base7RecipDigit m'` admits eventual period `P ≥ 1` and `Nat.Coprime m' 7`, then
`m' ∣ 7^P - 1`. -/
private lemma dvd_seven_pow_sub_one_of_eventualPeriod {m' P : ℕ} (hm' : 1 ≤ m')
    (hcop : Nat.Coprime m' 7) (hP : 1 ≤ P) (hper : Base7EventualPeriod m' P) :
    m' ∣ 7 ^ P - 1 := by
  rcases hper with ⟨K, hK1, hK⟩
  have hshift : ∀ s t : ℕ, 1 ≤ t →
      base7RecipDigit m' (K + s * P + t) = base7RecipDigit m' (K + t) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      intro t ht1
      rw [show K + (s + 1) * P + t = (K + s * P + t) + P by ring,
        hK (K + s * P + t) (by omega), ih t ht1]
  set B := digitBlock m' K P
  have hB_const : ∀ s : ℕ, digitBlock m' (K + s * P) P = B := fun s =>
    digitBlock_congr (fun t ht1 _ => hshift s t ht1)
  let r : ℕ → ℕ := fun s => 7 ^ (K + s * P) % m'
  have hr_step : ∀ s : ℕ, 7 ^ P * r s = m' * B + r (s + 1) := by
    intro s
    dsimp [r]
    rw [show K + (s + 1) * P = (K + s * P) + P by ring, ← hB_const s]
    exact rem_block_identity m' (K + s * P) P
  set Q := 7 ^ P
  have hQ_gt1 : 1 < Q := one_lt_seven_pow hP
  set Δ : ℤ := ((Q : ℤ) - 1) * (r 0 : ℤ) - (m' : ℤ) * (B : ℤ)
  have hΔ_pow : ∀ s : ℕ, (Q : ℤ) ^ s * Δ = ((Q : ℤ) - 1) * (r s : ℤ) - (m' : ℤ) * (B : ℤ) := by
    intro s
    induction s with
    | zero => simp [Δ]
    | succ s ih =>
      have hstep_z : (Q : ℤ) * (r s : ℤ) = (m' : ℤ) * (B : ℤ) + (r (s + 1) : ℤ) := by
        exact_mod_cast hr_step s
      calc
        (Q : ℤ) ^ (s + 1) * Δ = (Q : ℤ) * ((Q : ℤ) ^ s * Δ) := by rw [pow_succ']; ring
        _ = (Q : ℤ) * (((Q : ℤ) - 1) * (r s : ℤ) - (m' : ℤ) * (B : ℤ)) := by rw [ih]
        _ = ((Q : ℤ) - 1) * (r (s + 1) : ℤ) - (m' : ℤ) * (B : ℤ) := by
          linear_combination ((Q : ℤ) - 1) * hstep_z
  have hgrow_nat : m' * Q < Q ^ (m' + 1) := by
    have hlt_pow : m' < Q ^ m' := Nat.lt_pow_self hQ_gt1
    rw [pow_succ]
    exact Nat.mul_lt_mul_of_pos_right hlt_pow (by omega)
  have hgrow_z : (m' : ℤ) * (Q : ℤ) < (Q : ℤ) ^ (m' + 1) := by exact_mod_cast hgrow_nat
  have hr_lt_z : (r (m' + 1) : ℤ) < (m' : ℤ) := by
    exact_mod_cast Nat.mod_lt (7 ^ (K + (m' + 1) * P)) (by omega)
  have hr_nn : (0 : ℤ) ≤ (r (m' + 1) : ℤ) := Nat.cast_nonneg _
  have hB_lt_z : (B : ℤ) < (Q : ℤ) := by exact_mod_cast digitBlock_lt_pow m' K P
  have hB_nn : (0 : ℤ) ≤ (B : ℤ) := Nat.cast_nonneg _
  have hm'_z : (1 : ℤ) ≤ (m' : ℤ) := by exact_mod_cast hm'
  have hQ_z : (2 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hQ_gt1
  have hspec := hΔ_pow (m' + 1)
  have hrhs_hi : ((Q : ℤ) - 1) * (r (m' + 1) : ℤ) - (m' : ℤ) * (B : ℤ) < (Q : ℤ) ^ (m' + 1) := by
    nlinarith
  have hrhs_lo : -((Q : ℤ) ^ (m' + 1)) < ((Q : ℤ) - 1) * (r (m' + 1) : ℤ) - (m' : ℤ) * (B : ℤ) := by
    nlinarith
  have hQpow_pos : (0 : ℤ) < (Q : ℤ) ^ (m' + 1) := by positivity
  have hΔ_zero : Δ = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hle1 : Δ ≤ -1 := by omega
      have : (Q : ℤ) ^ (m' + 1) * Δ ≤ -((Q : ℤ) ^ (m' + 1)) := by nlinarith
      linarith
    · have hge1 : 1 ≤ Δ := by omega
      have : (Q : ℤ) ^ (m' + 1) ≤ (Q : ℤ) ^ (m' + 1) * Δ := by nlinarith
      linarith
  have heq_z : ((Q - 1 : ℕ) : ℤ) * (r 0 : ℤ) = (m' : ℤ) * (B : ℤ) := by
    rw [Int.ofNat_sub (by omega : 1 ≤ Q)]
    push_cast
    dsimp [Δ] at hΔ_zero
    linarith
  have heq_nat : (Q - 1) * (7 ^ K % m') = m' * B := by
    have hr0 : r 0 = 7 ^ K % m' := by simp [r]
    rw [← hr0]
    exact_mod_cast heq_z
  have hdvd_mul : m' ∣ (Q - 1) * 7 ^ K := by
    refine ⟨(Q - 1) * (7 ^ K / m') + B, ?_⟩
    have hdiv := Nat.div_add_mod (7 ^ K) m'
    calc
      (Q - 1) * 7 ^ K = (Q - 1) * (m' * (7 ^ K / m') + 7 ^ K % m') := by rw [hdiv]
      _ = m' * ((Q - 1) * (7 ^ K / m')) + (Q - 1) * (7 ^ K % m') := by ring
      _ = m' * ((Q - 1) * (7 ^ K / m')) + m' * B := by rw [heq_nat]
      _ = m' * ((Q - 1) * (7 ^ K / m') + B) := by ring
  exact (hcop.pow_right K).dvd_of_dvd_mul_right hdvd_mul

private lemma hasBase7RecipPeriodLen_iff_primitiveDivisor_of_coprime {m' n : ℕ}
    (hm' : 1 ≤ m') (hcop : Nat.Coprime m' 7) (hn : 1 ≤ n) :
    HasBase7RecipPeriodLen m' n ↔ IsPrimitiveDivisor7 n m' := by
  change (1 ≤ m' ∧
      ((n = 0 ∧ Base7Terminates m') ∨
        (1 ≤ n ∧ ¬ Base7Terminates m' ∧ Base7EventualPeriod m' n ∧
          ∀ p : ℕ, 1 ≤ p → p < n → ¬ Base7EventualPeriod m' p))) ↔
    (1 < m' ∧ m' ∣ (7 ^ n - 1) ∧ ∀ k : ℕ, 1 ≤ k → k < n → ¬ m' ∣ (7 ^ k - 1))
  have hn0 : n ≠ 0 := by omega
  simp only [hm', hn, hn0, false_and, true_and, false_or]
  rcases eq_or_lt_of_le hm' with rfl | hgt1
  · simp [terminates_one]
  · simp only [hgt1, not_terminates_of_gt_one_coprime hgt1 hcop, not_false_eq_true, true_and]
    constructor
    · rintro ⟨hper, hmin⟩
      refine ⟨dvd_seven_pow_sub_one_of_eventualPeriod hm' hcop hn hper, ?_⟩
      intro k hk1 hkn hdvd
      exact hmin k hk1 hkn (eventualPeriod_of_dvd_seven_pow_sub_one hm' hdvd)
    · rintro ⟨hdvd, hmin⟩
      refine ⟨eventualPeriod_of_dvd_seven_pow_sub_one hm' hdvd, ?_⟩
      intro p hp1 hpn hper
      exact hmin p hp1 hpn (dvd_seven_pow_sub_one_of_eventualPeriod hm' hcop hp1 hper)

/-- Half 1 (`SCOPING-S019.md` §2.1 Step 2): for every `n ≥ 1`,
`base7LeastPeriodDenominator n = minPrimDiv7 n`. -/
private theorem base7LeastPeriodDenominator_eq_minPrimDiv7 {n : ℕ} (hn : 1 ≤ n) :
    base7LeastPeriodDenominator n = minPrimDiv7 n := by
  apply nat_sInf_eq_of_mem_of_le
  · have hmem : IsPrimitiveDivisor7 n (minPrimDiv7 n) := minPrimDiv7_mem hn
    have hcop : Nat.Coprime (minPrimDiv7 n) 7 :=
      coprime_seven_of_dvd_seven_pow_sub_one hn hmem.2.1
    have hm1 : 1 ≤ minPrimDiv7 n := Nat.le_of_lt hmem.1
    exact (hasBase7RecipPeriodLen_iff_primitiveDivisor_of_coprime hm1 hcop hn).mpr hmem
  · intro m hm
    obtain ⟨v, m', rfl, hm'1, hcop⟩ := exists_seven_pow_mul_coprime hm.1
    have hm'_per : HasBase7RecipPeriodLen m' n :=
      (hasBase7RecipPeriodLen_seven_pow_mul_iff hm'1 v n).mp hm
    have hm'_prim : IsPrimitiveDivisor7 n m' :=
      (hasBase7RecipPeriodLen_iff_primitiveDivisor_of_coprime hm'1 hcop hn).mp hm'_per
    have hle : minPrimDiv7 n ≤ m' := minPrimDiv7_le hm'_prim
    have hm'_le : m' ≤ 7 ^ v * m' := Nat.le_mul_of_pos_left m' (seven_pow_pos v)
    exact le_trans hle hm'_le

/-! ### Step 3: Forward Polynomial-Order Inclusion (`SCOPING-S019.md` §2.1 Step 3) -/

private lemma adjoinRoot_dvd_X_pow_sub_one_iff {f : Polynomial (ZMod 7)} (e : ℕ) :
    f ∣ (Polynomial.X ^ e - 1) ↔ (AdjoinRoot.root f) ^ e = 1 := by
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, map_one, AdjoinRoot.mk_X, sub_eq_zero]

/-- Step 3 (`SCOPING-S019.md` §2.1): every monic degree-`n` (`n ≥ 2`) irreducible polynomial `f`
over `GF(7)` has `polyOrder f ∈ S(n)` (`f.coeff 0 ≠ 0` is automatic, and carried in the pin). -/
private theorem polyOrder_mem_primitiveDivisors7 {n : ℕ} (hn : 2 ≤ n)
    {f : Polynomial (ZMod 7)} (hf_monic : f.Monic) (hf_irred : Irreducible f)
    (hf_deg : f.natDegree = n) :
    IsPrimitiveDivisor7 n (polyOrder f) := by
  have : Fact (Irreducible f) := ⟨hf_irred⟩
  let pb := AdjoinRoot.powerBasis hf_monic.ne_zero
  have hcard_K : Nat.card (AdjoinRoot f) = 7 ^ n := by
    rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_fun, ZMod.card 7, Fintype.card_fin,
      AdjoinRoot.powerBasis_dim hf_monic.ne_zero, hf_deg]
  have : Finite (AdjoinRoot f) := Finite.of_equiv _ pb.basis.equivFun.symm.toEquiv
  have : CharP (AdjoinRoot f) 7 :=
    (Algebra.charP_iff (ZMod 7) (AdjoinRoot f) 7).mp (ZMod.charP 7)
  set α : AdjoinRoot f := AdjoinRoot.root f
  have hα_ne : α ≠ 0 := by
    intro h0
    have hdvdX : f ∣ Polynomial.X := by
      rw [← AdjoinRoot.mk_eq_zero, AdjoinRoot.mk_X]
      exact h0
    have hdeg_le : f.natDegree ≤ (Polynomial.X : Polynomial (ZMod 7)).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvdX Polynomial.X_ne_zero
    rw [Polynomial.natDegree_X, hf_deg] at hdeg_le
    omega
  let u : (AdjoinRoot f)ˣ := Units.mk0 α hα_ne
  have hu_pos : 0 < orderOf u := orderOf_pos u
  have hα_ord_eq : orderOf α = orderOf u := by
    have hu_val : (u : AdjoinRoot f) = α := Units.val_mk0 hα_ne
    rw [← hu_val, orderOf_units]
  have hd_pos : 1 ≤ orderOf α := by omega
  have hcard_units : Nat.card (AdjoinRoot f)ˣ = 7 ^ n - 1 := by
    rw [Nat.card_units, hcard_K]
  have hd_dvd_pow : orderOf α ∣ 7 ^ n - 1 := by
    rw [hα_ord_eq, ← hcard_units]
    exact orderOf_dvd_natCard u
  have hpolyOrder_eq : polyOrder f = orderOf α := by
    apply nat_sInf_eq_of_mem_of_le
    · refine ⟨hd_pos, ?_⟩
      rw [adjoinRoot_dvd_X_pow_sub_one_iff]
      exact pow_orderOf_eq_one α
    · rintro e ⟨he1, hdvd⟩
      rw [adjoinRoot_dvd_X_pow_sub_one_iff, ← orderOf_dvd_iff_pow_eq_one] at hdvd
      exact Nat.le_of_dvd he1 hdvd
  rw [hpolyOrder_eq]
  have hd_gt1 : 1 < orderOf α := by
    by_contra hle1
    have hd1 : orderOf α = 1 := by omega
    have hdvd1 : f ∣ (Polynomial.X - 1) := by
      have hα1 : AdjoinRoot.root f = 1 := orderOf_eq_one_iff.mp hd1
      simpa [hα1] using (adjoinRoot_dvd_X_pow_sub_one_iff (f := f) 1).mpr (by simp [hα1])
    have hdeg_le : f.natDegree ≤ (Polynomial.X - 1 : Polynomial (ZMod 7)).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd1 (Polynomial.X_sub_C_ne_zero 1)
    have hX1 : (Polynomial.X - 1 : Polynomial (ZMod 7)).natDegree = 1 := by
      simpa using Polynomial.natDegree_X_sub_C (1 : ZMod 7)
    omega
  refine ⟨hd_gt1, hd_dvd_pow, ?_⟩
  intro k hk1 hkn hdvd_k
  have hα_pow_sub : α ^ (7 ^ k - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd_k
  have hk_pos : 1 ≤ 7 ^ k := Nat.le_of_lt (one_lt_seven_pow hk1)
  have hα_frob : α ^ 7 ^ k = α := by
    calc
      α ^ 7 ^ k = α ^ (7 ^ k - 1 + 1) := by rw [Nat.sub_add_cancel hk_pos]
      _ = α ^ (7 ^ k - 1) * α := by rw [pow_succ]
      _ = α := by rw [hα_pow_sub, one_mul]
  have hall_frob : ∀ z : AdjoinRoot f, z ^ 7 ^ k = z := by
    intro z
    induction z using AdjoinRoot.induction_on with
    | ih g =>
      induction g using Polynomial.induction_on with
      | C c =>
        rw [← map_pow, ← Polynomial.C_pow, ZMod.pow_card_pow]
      | add p q hp hq =>
        rw [map_add, add_pow_char_pow, hp, hq]
      | monomial m c hm =>
        rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X, mul_pow, hm, hα_frob]
  set P : Polynomial (AdjoinRoot f) := Polynomial.X ^ 7 ^ k - Polynomial.X
  have hk_gt1 : 1 < 7 ^ k := one_lt_seven_pow hk1
  have hP_ne : P ≠ 0 := by
    intro h0
    have hc : P.coeff (7 ^ k) = 0 := by rw [h0, Polynomial.coeff_zero]
    dsimp [P] at hc
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, Polynomial.coeff_X] at hc
    simp only [show ¬ (1 = 7 ^ k) by omega, ↓reduceIte, sub_zero] at hc
    exact one_ne_zero hc
  have hP_deg : P.natDegree ≤ 7 ^ k := by
    dsimp [P]
    calc
      (Polynomial.X ^ 7 ^ k - Polynomial.X : Polynomial (AdjoinRoot f)).natDegree
          ≤ max (Polynomial.X ^ 7 ^ k : Polynomial (AdjoinRoot f)).natDegree
              (Polynomial.X : Polynomial (AdjoinRoot f)).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ = max (7 ^ k) 1 := by rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      _ ≤ 7 ^ k := by omega
  let _ : Fintype (AdjoinRoot f) := Fintype.ofFinite (AdjoinRoot f)
  have hsub : (Finset.univ : Finset (AdjoinRoot f)) ⊆ P.roots.toFinset := by
    intro z _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne]
    simp [P, Polynomial.IsRoot, hall_frob z]
  have hcard_le : Fintype.card (AdjoinRoot f) ≤ 7 ^ k := by
    calc
      Fintype.card (AdjoinRoot f) = (Finset.univ : Finset (AdjoinRoot f)).card := rfl
      _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le P.roots
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ ≤ 7 ^ k := hP_deg
  rw [Fintype.card_eq_nat_card, hcard_K] at hcard_le
  have hlt : 7 ^ k < 7 ^ n := Nat.pow_lt_pow_right (by decide : 1 < 7) hkn
  omega

/-! ### Step 4: Converse Polynomial-Order Realization (`SCOPING-S019.md` §2.1 Step 4) -/

/-- Step 4 (`SCOPING-S019.md` §2.1): every `d ∈ S(n)` (`n ≥ 2`) is realized as `polyOrder f` for a
monic degree-`n` irreducible polynomial `f` over `GF(7)` with `f.coeff 0 ≠ 0`. -/
private theorem exists_irred_of_primitiveDivisor7 {n d : ℕ} (hn : 2 ≤ n)
    (hd : IsPrimitiveDivisor7 n d) :
    ∃ f : Polynomial (ZMod 7),
      f.Monic ∧ Irreducible f ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 ∧ d = polyOrder f := by
  rcases hd with ⟨hd1, hd_dvd, hd_prim⟩
  have hn0 : n ≠ 0 := by omega
  let E := GaloisField 7 n
  have hcardE : Nat.card E = 7 ^ n := GaloisField.card 7 n hn0
  have hfinrankE : Module.finrank (ZMod 7) E = n := GaloisField.finrank 7 hn0
  have hcardUnits : Nat.card Eˣ = 7 ^ n - 1 := by
    rw [Nat.card_units, hcardE]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Eˣ)
  rw [hcardUnits] at hg
  have hpow_gt : 1 < 7 ^ n := one_lt_seven_pow (by omega)
  have hg_ne : orderOf g ≠ 0 := by omega
  have hd_dvd_g : d ∣ orderOf g := by rwa [hg]
  let u : Eˣ := g ^ (orderOf g / d)
  let α : E := (u : E)
  have hu_ord : orderOf u = d := orderOf_pow_orderOf_div hg_ne hd_dvd_g
  have hα_ord : orderOf α = d := by rw [orderOf_units, hu_ord]
  have hα_ne : α ≠ 0 := Units.ne_zero u
  have hx_int : IsIntegral (ZMod 7) α := Algebra.IsIntegral.isIntegral α
  set f : Polynomial (ZMod 7) := minpoly (ZMod 7) α
  have hf_monic : f.Monic := minpoly.monic hx_int
  have hf_irred : Irreducible f := minpoly.irreducible hx_int
  have hdvd_iff : ∀ e : ℕ, f ∣ (Polynomial.X ^ e - 1) ↔ d ∣ e := by
    intro e
    rw [minpoly.dvd_iff, map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero,
      ← orderOf_dvd_iff_pow_eq_one, hα_ord]
  have hpolyOrder : polyOrder f = d := by
    apply nat_sInf_eq_of_mem_of_le
    · exact ⟨by omega, (hdvd_iff d).mpr dvd_rfl⟩
    · rintro e ⟨he1, hf_dvd⟩
      exact Nat.le_of_dvd he1 ((hdvd_iff e).mp hf_dvd)
  have hcoeff0 : f.coeff 0 ≠ 0 := by
    intro hc0
    rcases (hdvd_iff d).mpr dvd_rfl with ⟨q, hq⟩
    have heval := congrArg (Polynomial.eval (0 : ZMod 7)) hq
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      zero_pow (by omega : d ≠ 0), zero_sub, Polynomial.eval_mul,
      ← Polynomial.coeff_zero_eq_eval_zero, hc0, zero_mul] at heval
    exact (by decide : (-1 : ZMod 7) ≠ 0) heval
  let Fα : IntermediateField (ZMod 7) E := IntermediateField.adjoin (ZMod 7) {α}
  have hfinrank_Fα : Module.finrank (ZMod 7) Fα = f.natDegree :=
    IntermediateField.adjoin.finrank hx_int
  set k := f.natDegree
  have hk_pos : 0 < k := minpoly.natDegree_pos hx_int
  have htower : Module.finrank (ZMod 7) Fα * Module.finrank Fα E = Module.finrank (ZMod 7) E :=
    Module.finrank_mul_finrank (ZMod 7) Fα E
  rw [hfinrank_Fα, hfinrankE] at htower
  have htop_pos : 0 < Module.finrank Fα E := by
    by_contra h0
    have hz : Module.finrank Fα E = 0 := by omega
    rw [hz, mul_zero] at htower
    omega
  have hk_le_n : k ≤ n := by
    rw [← htower]
    exact Nat.le_mul_of_pos_right k htop_pos
  have hcard_Fα : Nat.card Fα = 7 ^ k := by
    rw [← FiniteField.pow_finrank_eq_natCard 7 Fα, hfinrank_Fα]
  have hcard_Fα_units : Nat.card Fαˣ = 7 ^ k - 1 := by
    rw [Nat.card_units, hcard_Fα]
  let αF : Fα := ⟨α, IntermediateField.mem_adjoin_simple_self (ZMod 7) α⟩
  have hαF_ne : αF ≠ 0 := fun h => hα_ne (congrArg Subtype.val h)
  let uF : Fαˣ := Units.mk0 αF hαF_ne
  have huF_ord : orderOf uF = d := by
    have huF_val : (uF : Fα) = αF := Units.val_mk0 hαF_ne
    have hinj : Function.Injective Fα.val.toMonoidHom := Subtype.val_injective
    rw [← orderOf_units, huF_val, ← orderOf_injective Fα.val.toMonoidHom hinj αF]
    exact hα_ord
  have hd_dvd_k : d ∣ 7 ^ k - 1 := by
    rw [← huF_ord, ← hcard_Fα_units]
    exact orderOf_dvd_natCard uF
  have hk_eq_n : k = n := by
    rcases eq_or_lt_of_le hk_le_n with heq | hlt
    · exact heq
    · exact False.elim (hd_prim k (by omega) hlt hd_dvd_k)
  exact ⟨f, hf_monic, hf_irred, hk_eq_n, hcoeff0, hpolyOrder.symm⟩

/-- Half 2 (`SCOPING-S019.md` §2.1 Steps 3–5): for every `n ≥ 2`,
`minIrredOrder n = minPrimDiv7 n`. -/
private theorem minIrredOrder_eq_minPrimDiv7 {n : ℕ} (hn : 2 ≤ n) :
    minIrredOrder n = minPrimDiv7 n := by
  apply nat_sInf_eq_of_mem_of_le
  · exact exists_irred_of_primitiveDivisor7 hn (minPrimDiv7_mem (by omega))
  · rintro d ⟨f, hf_monic, hf_irred, hf_deg, _, rfl⟩
    exact minPrimDiv7_le (polyOrder_mem_primitiveDivisors7 hn hf_monic hf_irred hf_deg)

/-! ### Step 5: Synthesis & Frozen Target Theorems (`PIN-S019.md` v1) -/

/-- Calibration theorem (`n = 2` base value; `PIN-S019.md` v1):
`base7LeastPeriodDenominator 2 = 4`. -/
theorem base7LeastPeriodDenominator_two :
    base7LeastPeriodDenominator 2 = 4 := by
  rw [base7LeastPeriodDenominator_eq_minPrimDiv7 (by decide : 1 ≤ 2)]
  apply nat_sInf_eq_of_mem_of_le
  · refine ⟨by decide, by decide, ?_⟩
    intro k hk1 hk2
    have hk : k = 1 := by omega
    subst hk
    decide
  · rintro d ⟨hd1, _, hd_prim⟩
    have hndvd6 : ¬ d ∣ 6 := hd_prim 1 le_rfl (by decide)
    by_contra hlt4
    have hd23 : d = 2 ∨ d = 3 := by omega
    rcases hd23 with rfl | rfl <;> exact hndvd6 (by decide)

/-- Main theorem (`OEIS A381494` `%F` line 14, R. J. Mathar, Mar 03 2025; `PIN-S019.md` v1):
for every `n : ℕ` with `2 ≤ n`, `base7LeastPeriodDenominator n = minIrredOrder n`. -/
theorem base7LeastPeriodDenominator_eq_minIrredOrder :
    ∀ n : ℕ, 2 ≤ n → base7LeastPeriodDenominator n = minIrredOrder n := by
  intro n hn
  rw [base7LeastPeriodDenominator_eq_minPrimDiv7 (by omega), minIrredOrder_eq_minPrimDiv7 hn]

/-! ### Boundary Theorems, `√M` Computable Mirror, and `OEIS` Non-Vacuity Spot Checks -/

/-- Companion calibration value `minIrredOrder 2 = 4` (`OEIS A218358(2) = 4`). -/
theorem minIrredOrder_two :
    minIrredOrder 2 = 4 := by
  rw [← base7LeastPeriodDenominator_eq_minIrredOrder 2 le_rfl, base7LeastPeriodDenominator_two]

/-- Fidelity check (`PIN-S019.md` fidelity note 3): for `2 ≤ f.natDegree`, `Irreducible f`
automatically implies `f.coeff 0 ≠ 0` (the explicit guard only acts at `n = 1` to exclude `X`). -/
theorem irred_coeff_zero_ne_zero_of_two_le {f : Polynomial (ZMod 7)}
    (hf_irred : Irreducible f) (hdeg : 2 ≤ f.natDegree) :
    f.coeff 0 ≠ 0 := by
  intro hc0
  rcases Polynomial.X_dvd_iff.mpr hc0 with ⟨q, hfq⟩
  rcases hf_irred.isUnit_or_isUnit hfq with hX_unit | hq_unit
  · exact Polynomial.not_isUnit_X hX_unit
  · have hq_deg : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hq_unit
    have hf_deg : f.natDegree = 1 := by
      rw [hfq, Polynomial.natDegree_mul Polynomial.X_ne_zero hq_unit.ne_zero,
        Polynomial.natDegree_X, hq_deg]
    omega

/-- Boundary value `A381494(0) = 1` (`1/1` terminates in base 7). -/
theorem base7LeastPeriodDenominator_zero :
    base7LeastPeriodDenominator 0 = 1 := by
  apply nat_sInf_eq_of_mem_of_le
  · exact ⟨le_rfl, Or.inl ⟨rfl, terminates_one⟩⟩
  · intro m hm
    exact hm.1

/-- Boundary value `A381494(1) = 2` (`1/2 = .333..._7` has minimal period `1`). -/
theorem base7LeastPeriodDenominator_one :
    base7LeastPeriodDenominator 1 = 2 := by
  rw [base7LeastPeriodDenominator_eq_minPrimDiv7 le_rfl]
  apply nat_sInf_eq_of_mem_of_le
  · refine ⟨by decide, by decide, ?_⟩
    intro k hk1 hklt
    omega
  · rintro d ⟨hd1, _, _⟩
    omega

private lemma zmod7_pow_six_eq_one (c : ZMod 7) (hc : c ≠ 0) : c ^ 6 = 1 := by
  revert hc
  revert c
  decide

/-- Boundary value `A218358(1) = 1` (`X - 1` is monic irreducible of degree `1` with order `1`). -/
theorem minIrredOrder_one :
    minIrredOrder 1 = 1 := by
  apply nat_sInf_eq_of_mem_of_le
  · refine ⟨Polynomial.X - 1, Polynomial.monic_X_sub_C 1, Polynomial.irreducible_X_sub_C 1,
      by simpa using Polynomial.natDegree_X_sub_C (1 : ZMod 7), ?_, ?_⟩
    · rw [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero, zero_sub]
      decide
    · symm
      apply nat_sInf_eq_of_mem_of_le
      · exact ⟨le_rfl, by simp⟩
      · rintro e ⟨he1, _⟩
        exact he1
  · rintro d ⟨f, hf_monic, _, hf_deg, hf_c0, rfl⟩
    set c : ZMod 7 := -f.coeff 0
    have hc_ne : c ≠ 0 := neg_ne_zero.mpr hf_c0
    have hf_eq : f = Polynomial.X - Polynomial.C c := by
      ext i
      rcases i with _ | _ | i
      · simp [c]
      · have h1 : f.coeff 1 = 1 := by
          rw [← hf_deg]
          exact hf_monic.leadingCoeff
        simp [h1]
      · have hgt : f.natDegree < i + 2 := by omega
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, Polynomial.coeff_X]
    have hc6 : Polynomial.C c ^ 6 = (1 : Polynomial (ZMod 7)) := by
      rw [← Polynomial.C_pow, zmod7_pow_six_eq_one c hc_ne, map_one]
    have hdvd6 : f ∣ (Polynomial.X ^ 6 - 1) := by
      refine ⟨Polynomial.X ^ 5 + Polynomial.C c * Polynomial.X ^ 4 +
        Polynomial.C c ^ 2 * Polynomial.X ^ 3 + Polynomial.C c ^ 3 * Polynomial.X ^ 2 +
        Polynomial.C c ^ 4 * Polynomial.X + Polynomial.C c ^ 5, ?_⟩
      rw [hf_eq]
      linear_combination hc6
    have hmem : 1 ≤ polyOrder f ∧ f ∣ (Polynomial.X ^ polyOrder f - 1) :=
      Nat.sInf_mem (s := { e : ℕ | 1 ≤ e ∧ f ∣ (Polynomial.X ^ e - 1) }) ⟨6, by decide, hdvd6⟩
    exact hmem.1

/-- Sharp domain-guard witness (`PIN-S019.md` fidelity note 1):
at `n = 1`, `A381494(1) = 2 ≠ 1 = A218358(1)`, confirming `2 ≤ n` is sharp. -/
theorem sharp_guard_at_one :
    base7LeastPeriodDenominator 1 = 2 ∧
      minIrredOrder 1 = 1 ∧
      base7LeastPeriodDenominator 1 ≠ minIrredOrder 1 := by
  rw [base7LeastPeriodDenominator_one, minIrredOrder_one]
  exact ⟨rfl, rfl, by decide⟩

/-- Direct kernel `rfl` verification of `base7RecipDigit` on `m = 1, 2, 4, 9`
(reproducing `OEIS A381494` `%e`: `1/9 = .053053..._7`). -/
theorem base7RecipDigit_literal_examples :
    [1, 2, 3, 4, 5, 6].map (base7RecipDigit 9) = [0, 5, 3, 0, 5, 3] ∧
      [1, 2, 3, 4].map (base7RecipDigit 4) = [1, 5, 1, 5] ∧
      [1, 2, 3].map (base7RecipDigit 2) = [3, 3, 3] ∧
      [1, 2, 3].map (base7RecipDigit 1) = [0, 0, 0] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Structural computable primitive-divisor test (`M = 7^n - 1` precomputed once per `n`). -/
def isPrimDiv7B (n M d : ℕ) : Bool :=
  decide (1 < d) && (M % d == 0) &&
    ((List.range (n - 1)).map (· + 1)).all (fun k => (7 ^ k - 1) % d != 0)

private lemma isPrimDiv7B_iff {n d : ℕ} :
    isPrimDiv7B n (7 ^ n - 1) d = true ↔ IsPrimitiveDivisor7 n d := by
  unfold isPrimDiv7B IsPrimitiveDivisor7
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_map, List.mem_range, bne_iff_ne]
  refine ⟨fun ⟨⟨hd1, hmod⟩, hall⟩ =>
      ⟨hd1, Nat.dvd_of_mod_eq_zero hmod, ?_⟩,
    fun ⟨hd1, hdvd, hall⟩ =>
      ⟨⟨hd1, Nat.mod_eq_zero_of_dvd hdvd⟩, ?_⟩⟩
  · intro k hk1 hkn hdvd_k
    exact hall k ⟨k - 1, by omega, by omega⟩ (Nat.mod_eq_zero_of_dvd hdvd_k)
  · rintro k ⟨j, hj, rfl⟩ hmod_k
    exact hall (j + 1) (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hmod_k)

/-- Pass 1 of the `O(√M)` computable mirror: scans `d = 2, 3, ...` while `d^2 ≤ M`, returning
`Sum.inl d` on the first hit or `Sum.inr s` at the first `s` with `M < s^2`. -/
def findSmallPrimDiv (n M d : ℕ) : ℕ → ℕ ⊕ ℕ
  | 0 => Sum.inr d
  | fuel + 1 =>
    if decide (M < d * d) then Sum.inr d
    else if isPrimDiv7B n M d then Sum.inl d
    else findSmallPrimDiv n M (d + 1) fuel

/-- Pass 2 of the `O(√M)` computable mirror: scans complementary divisors `M / q` in ascending
order by decrementing `q` from `s - 1` down to `1`. -/
def findLargePrimDiv (n M : ℕ) : ℕ → ℕ
  | 0 => M
  | q + 1 =>
    if (M % (q + 1) == 0) && isPrimDiv7B n M (M / (q + 1)) then
      M / (q + 1)
    else
      findLargePrimDiv n M q

/-- Total `O(√(7^n - 1))` structural computable mirror of `base7LeastPeriodDenominator` (`n ≥ 0`)
and `minIrredOrder` (`n ≥ 2`), keeping kernel stack depth `≤ √(7^n - 1)` (`≤ 130` at `n = 5`). -/
def a381494Compute (n : ℕ) : ℕ :=
  if n = 0 then 1
  else if n = 1 then 2
  else
    let M := 7 ^ n - 1
    match findSmallPrimDiv n M 2 M with
    | Sum.inl d => d
    | Sum.inr s => findLargePrimDiv n M (s - 1)

private lemma findSmallPrimDiv_spec {n : ℕ} (hn : 2 ≤ n) :
    ∀ fuel d : ℕ, 2 ≤ d → 7 ^ n - 1 < d + fuel →
      (∀ c : ℕ, 2 ≤ c → c < d → ¬ IsPrimitiveDivisor7 n c) →
      match findSmallPrimDiv n (7 ^ n - 1) d fuel with
      | Sum.inl r => r = minPrimDiv7 n
      | Sum.inr s => 2 ≤ s ∧ 7 ^ n - 1 < s * s ∧
          ∀ c : ℕ, 2 ≤ c → c < s → ¬ IsPrimitiveDivisor7 n c
  | 0, d, hd2, hlt, hnone => by
    unfold findSmallPrimDiv
    have hdd : d ≤ d * d := by nlinarith
    exact ⟨hd2, by omega, hnone⟩
  | fuel + 1, d, hd2, hlt, hnone => by
    unfold findSmallPrimDiv
    by_cases hsq : 7 ^ n - 1 < d * d
    · simp only [decide_eq_true hsq, ↓reduceIte]
      exact ⟨hd2, hsq, hnone⟩
    · simp only [decide_eq_false hsq, Bool.false_eq_true, ↓reduceIte]
      by_cases hcur : isPrimDiv7B n (7 ^ n - 1) d = true
      · rw [hcur]
        simp only [↓reduceIte]
        have hd_prim : IsPrimitiveDivisor7 n d := isPrimDiv7B_iff.mp hcur
        symm
        apply nat_sInf_eq_of_mem_of_le hd_prim
        intro m hm
        by_contra hlt_m
        exact hnone m (by have := hm.1; omega) (by omega) hm
      · have hfalse : isPrimDiv7B n (7 ^ n - 1) d = false := Bool.eq_false_iff.mpr hcur
        rw [hfalse]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hnot_d : ¬ IsPrimitiveDivisor7 n d := fun hp => hcur (isPrimDiv7B_iff.mpr hp)
        refine findSmallPrimDiv_spec hn fuel (d + 1) (by omega) (by omega) ?_
        intro c hc2 hclt
        rcases eq_or_lt_of_le (show c ≤ d by omega) with rfl | hlt_d
        · exact hnot_d
        · exact hnone c hc2 hlt_d

private lemma div_le_div_of_dvd_of_ge {M q₁ q₂ : ℕ} (hM : 0 < M)
    (hd₁ : q₁ ∣ M) (hd₂ : q₂ ∣ M) (hle : q₂ ≤ q₁) : M / q₁ ≤ M / q₂ := by
  have hq₂ : 0 < q₂ := Nat.pos_of_dvd_of_pos hd₂ hM
  have hmul₁ : (M / q₁) * q₁ = M := Nat.div_mul_cancel hd₁
  have hmul₂ : (M / q₂) * q₂ = M := Nat.div_mul_cancel hd₂
  by_contra hgt
  have hlt : M / q₂ < M / q₁ := by omega
  have h1 : (M / q₂) * q₂ < (M / q₁) * q₂ := Nat.mul_lt_mul_of_pos_right hlt hq₂
  have h2 : (M / q₁) * q₂ ≤ (M / q₁) * q₁ := Nat.mul_le_mul_left _ hle
  omega

private lemma findLargePrimDiv_spec {n : ℕ} (hn : 2 ≤ n) :
    ∀ q : ℕ,
      (∀ r : ℕ, q < r → r ∣ (7 ^ n - 1) → ¬ IsPrimitiveDivisor7 n ((7 ^ n - 1) / r)) →
      findLargePrimDiv n (7 ^ n - 1) q = minPrimDiv7 n
  | 0, hnone => by
    unfold findLargePrimDiv
    have hM_pos : 0 < 7 ^ n - 1 := by
      have := one_lt_seven_pow (show 1 ≤ n by omega)
      omega
    symm
    apply nat_sInf_eq_of_mem_of_le (self_mem_primitiveDivisors7 (by omega))
    intro m hm
    rcases hm.2.1 with ⟨r, hr⟩
    have hr_pos : 0 < r := by
      by_contra hr0
      have hr_z : r = 0 := by omega
      rw [hr_z, mul_zero] at hr
      omega
    have hr_dvd : r ∣ 7 ^ n - 1 := ⟨m, by rw [hr, mul_comm]⟩
    have hm_eq : (7 ^ n - 1) / r = m := by
      rw [hr, Nat.mul_div_cancel _ hr_pos]
    have hnot := hnone r hr_pos hr_dvd
    rw [hm_eq] at hnot
    exact False.elim (hnot hm)
  | q + 1, hnone => by
    unfold findLargePrimDiv
    set M := 7 ^ n - 1
    have hM_pos : 0 < M := by
      have := one_lt_seven_pow (show 1 ≤ n by omega)
      omega
    by_cases hhit : ((M % (q + 1) == 0) && isPrimDiv7B n M (M / (q + 1))) = true
    · rw [hhit]
      simp only [↓reduceIte]
      rw [Bool.and_eq_true, beq_iff_eq] at hhit
      have hqdvd : q + 1 ∣ M := Nat.dvd_of_mod_eq_zero hhit.1
      have hd_prim : IsPrimitiveDivisor7 n (M / (q + 1)) := isPrimDiv7B_iff.mp hhit.2
      symm
      apply nat_sInf_eq_of_mem_of_le hd_prim
      intro m hm
      rcases hm.2.1 with ⟨r, hr⟩
      have hr_pos : 0 < r := by
        by_contra hr0
        have hr_z : r = 0 := by omega
        rw [hr_z, mul_zero] at hr
        omega
      have hr_dvd : r ∣ M := ⟨m, by dsimp [M]; rw [hr, mul_comm]⟩
      have hm_eq : M / r = m := by dsimp [M]; rw [hr, Nat.mul_div_cancel _ hr_pos]
      rcases lt_or_ge (q + 1) r with hgt | hle
      · have hnot := hnone r hgt hr_dvd
        rw [hm_eq] at hnot
        exact False.elim (hnot hm)
      · rw [← hm_eq]
        exact div_le_div_of_dvd_of_ge hM_pos hqdvd hr_dvd hle
    · have hfalse : ((M % (q + 1) == 0) && isPrimDiv7B n M (M / (q + 1))) = false :=
        Bool.eq_false_iff.mpr hhit
      rw [hfalse]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine findLargePrimDiv_spec hn q ?_
      intro r hrgt hrdvd hprim
      rcases eq_or_lt_of_le (show q + 1 ≤ r by omega) with rfl | hgt
      · apply hhit
        rw [Bool.and_eq_true, beq_iff_eq]
        exact ⟨Nat.mod_eq_zero_of_dvd hrdvd, isPrimDiv7B_iff.mpr hprim⟩
      · exact hnone r hgt hrdvd hprim

/-- Formal equivalence between `base7LeastPeriodDenominator` and its `O(√M)` computable mirror
`a381494Compute` for all `n : ℕ`. -/
theorem base7LeastPeriodDenominator_eq_compute (n : ℕ) :
    base7LeastPeriodDenominator n = a381494Compute n := by
  rcases n with _ | _ | m
  · exact base7LeastPeriodDenominator_zero
  · exact base7LeastPeriodDenominator_one
  · set k := m + 2
    have hk2 : 2 ≤ k := by omega
    have hM_pos : 0 < 7 ^ k - 1 := by
      have := one_lt_seven_pow (show 1 ≤ k by omega)
      omega
    unfold a381494Compute
    simp only [show k ≠ 0 by omega, show k ≠ 1 by omega, ↓reduceIte]
    rw [base7LeastPeriodDenominator_eq_minPrimDiv7 (by omega)]
    have hsmall := findSmallPrimDiv_spec hk2 (7 ^ k - 1) 2 le_rfl (by omega)
      (fun _ hc2 hlt => by omega)
    cases hres : findSmallPrimDiv k (7 ^ k - 1) 2 (7 ^ k - 1) with
    | inl r =>
      rw [hres] at hsmall
      exact hsmall.symm
    | inr s =>
      rw [hres] at hsmall
      rcases hsmall with ⟨hs2, hsq, hnone_small⟩
      symm
      refine findLargePrimDiv_spec hk2 (s - 1) ?_
      intro r hrgt hrdvd hprim
      have hs_le_r : s ≤ r := by omega
      have hmul : ((7 ^ k - 1) / r) * r = 7 ^ k - 1 := Nat.div_mul_cancel hrdvd
      have hd_lt_s : (7 ^ k - 1) / r < s := by
        by_contra hge
        have hs_le_d : s ≤ (7 ^ k - 1) / r := by omega
        have : s * s ≤ ((7 ^ k - 1) / r) * r := Nat.mul_le_mul hs_le_d hs_le_r
        omega
      exact hnone_small ((7 ^ k - 1) / r) (by have := hprim.1; omega) hd_lt_s hprim

/-- Formal equivalence between `minIrredOrder` and `a381494Compute` for all `n ≥ 2`. -/
theorem minIrredOrder_eq_compute {n : ℕ} (hn : 2 ≤ n) :
    minIrredOrder n = a381494Compute n := by
  rw [← base7LeastPeriodDenominator_eq_minIrredOrder n hn, base7LeastPeriodDenominator_eq_compute]

/-- Kernel-verified spot checks of both pinned sequences across `n = 2..10` against the live OEIS
values `[4, 9, 5, 2801, 36, 29, 64, 27, 11]` (`PIN-S019.md` fidelity note 4) via the formally
verified computable mirror `a381494Compute` (no `native_decide`). -/
theorem oeis_spot_checks_2_to_10 :
    [2, 3, 4, 5, 6, 7, 8, 9, 10].map base7LeastPeriodDenominator =
      [4, 9, 5, 2801, 36, 29, 64, 27, 11] ∧
    [2, 3, 4, 5, 6, 7, 8, 9, 10].map minIrredOrder =
      [4, 9, 5, 2801, 36, 29, 64, 27, 11] := by
  have hL : [2, 3, 4, 5, 6, 7, 8, 9, 10].map base7LeastPeriodDenominator =
      [2, 3, 4, 5, 6, 7, 8, 9, 10].map a381494Compute := by
    simp [base7LeastPeriodDenominator_eq_compute]
  have hR : [2, 3, 4, 5, 6, 7, 8, 9, 10].map minIrredOrder =
      [2, 3, 4, 5, 6, 7, 8, 9, 10].map a381494Compute := by
    refine List.map_congr_left fun n hn => minIrredOrder_eq_compute ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [hL, hR]
  exact ⟨by decide, by decide⟩

/-- Kernel-verified refutation of the integer cyclotomic-divisor condition `a(n) ∣ Φ_n(7)`
(`SCOPING-S019.md` §1.2 Error 3 & §2.1 Step 5):
at `n = 3`, `a(3) = 9 ∤ 57 = Φ_3(7)`; at `n = 6`, `a(6) = 36` is coprime to `Φ_6(7) = 43`. -/
theorem refute_cyclotomic_divisor_shortcut :
    base7LeastPeriodDenominator 3 = 9 ∧ ¬ (9 ∣ (7 ^ 2 + 7 + 1)) ∧
    base7LeastPeriodDenominator 6 = 36 ∧ Nat.Coprime 36 (7 ^ 2 - 7 + 1) := by
  rw [base7LeastPeriodDenominator_eq_compute 3, base7LeastPeriodDenominator_eq_compute 6]
  exact ⟨by decide, by decide, by decide, by decide⟩

end SeamC.A381494
