import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Order.Lattice.Nat

/-!
# Seam C `S019` (`OEIS A381494 = A218358`): Base-7 Reciprocal Period and `GF(7)` Irreducible Order

Statement contract frozen from `PIN-S019.md` v1 (`delta_vs_source: NONE`) for R. J. Mathar's
Mar 03 2025 conjecture on `OEIS A381494` (`%F` line 14, live revision `#23 Mar 02 2026 13:15:08`)
and companion `OEIS A218358` (`%N` line 10, `%F` line 15, live revision `#17 Feb 16 2025 08:33:18`).
-/

namespace SeamC.A381494

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

/-- Calibration theorem (`n = 2` base value; `PIN-S019.md` v1):
`base7LeastPeriodDenominator 2 = 4`. -/
theorem base7LeastPeriodDenominator_two :
    base7LeastPeriodDenominator 2 = 4 := by
  sorry

/-- Main theorem (`OEIS A381494` `%F` line 14, R. J. Mathar, Mar 03 2025; `PIN-S019.md` v1):
for every `n : ℕ` with `2 ≤ n`, `base7LeastPeriodDenominator n = minIrredOrder n`. -/
theorem base7LeastPeriodDenominator_eq_minIrredOrder :
    ∀ n : ℕ, 2 ≤ n → base7LeastPeriodDenominator n = minIrredOrder n := by
  sorry

end SeamC.A381494
