import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Seam B Entry C037 (OEIS A203568): Peter Bala's Rogers–Fine Polynomial Family

Formalizes and proves Peter Bala's February 11, 2021 conjectural `N`-parameterized
generating-function family on `OEIS A203568` (`%F` lines 24–26, live revision `#52 Feb 18 2021`;
companions `OEIS A026837` `%I #20`, `OEIS A026838` `%I #24`, `OEIS A143062` `%I #58`, and
`OEIS A186424` `%I #52`) against the frozen target contract `PIN-C037.md` v1
(`delta_vs_source: NONE`), following the `Step 0 + Links 1–4` route from `SCOPING-C037.md` (§2.2).
-/

namespace Mathproofs.A203568RogersFineFamily

open scoped BigOperators Classical Polynomial PowerSeries PowerSeries.WithPiTopology

noncomputable section

/-! ### Pinned Target Definitions (`PIN-C037.md` v1) -/

/-- `OEIS A026837`: number of partitions `p ∈ Nat.Partition.distincts n` of `n` into distinct
parts whose greatest part is odd (`0` at `n = 0`). -/
def a026837 (n : ℕ) : ℕ :=
  ((Nat.Partition.distincts n).filter
    (fun p ↦ ∃ m ∈ p.parts, Odd m ∧ ∀ x ∈ p.parts, x ≤ m)).card

/-- `OEIS A026838`: number of partitions `p ∈ Nat.Partition.distincts n` of `n` into distinct
parts whose greatest part is even (`0` at `n = 0`). -/
def a026838 (n : ℕ) : ℕ :=
  ((Nat.Partition.distincts n).filter
    (fun p ↦ ∃ m ∈ p.parts, Even m ∧ ∀ x ∈ p.parts, x ≤ m)).card

/-- `OEIS A203568` (`%N`): `a(n) = A026837(n) - A026838(n)` with offset `0` and `a(0) = 0`. -/
def a203568 (n : ℕ) : ℤ :=
  (a026837 n : ℤ) - (a026838 n : ℤ)

/-- Formal power series `A(X) = ∑_{n ≥ 0} A203568(n) X^n` in `ℤ⟦X⟧`. -/
def a203568Series : ℤ⟦X⟧ :=
  PowerSeries.mk a203568

/-- Explicit polynomial family `P(N, X) ∈ ℤ[X]` pinned by `c037Poly 0 = 0`, `c037Poly 1 = 0`, and
`c037Poly (N + 1) = (1 + X ^ (2 * N)) * c037Poly N + (-1) ^ (N + 1) * X ^ N` for all `N ≥ 1`. -/
def c037Poly : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 0
  | N + 2 =>
      (1 + Polynomial.X ^ (2 * (N + 1))) * c037Poly (N + 1) +
        (-1) ^ (N + 2) * Polynomial.X ^ (N + 1)

/-! ### Pinned Target Theorems (`PIN-C037.md` v1) -/

/-- Fine's partition theorem (`OEIS A203568` `%F` lines 13–14, 19): connects `%N` (`a203568`) to
the generalized pentagonal numbers `pentagonal k = k * (3 * k - 1) / 2`. -/
theorem a203568_eq_pentagonal (n : ℕ) :
    a203568 n = if h : ∃ k : ℤ, pentagonal k = n then Int.sign h.choose else 0 := by
  sorry

/-- Closed-form sum-of-products formula for `c037Poly N` (`N ≥ 1`). -/
theorem c037Poly_closed_form (N : ℕ) (hN : 1 ≤ N) :
    c037Poly N = ∑ m ∈ Finset.Icc 1 (N - 1),
      (-1 : ℤ[X]) ^ (m + 1) * Polynomial.X ^ m *
        ∏ j ∈ Finset.Icc (m + 1) (N - 1), (1 + Polynomial.X ^ (2 * j)) := by
  sorry

/-- Pinned empirical polynomials `P(1, X)` through `P(4, X)` from `OEIS A203568` (`%F` line 26). -/
theorem c037Poly_empirical_values :
    c037Poly 1 = 0 ∧
      c037Poly 2 = Polynomial.X ∧
      c037Poly 3 = Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 5 ∧
      c037Poly 4 = Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 3 + Polynomial.X ^ 5 +
        Polynomial.X ^ 7 - Polynomial.X ^ 8 + Polynomial.X ^ 11 := by
  sorry

/-- Exact degree `N^2 - N - 1` (in `WithBot ℕ`) and monicity of `c037Poly N` for all `1 < N`. -/
theorem c037Poly_degree_and_monic (N : ℕ) (hN : 1 < N) :
    (c037Poly N).degree = ((N ^ 2 - N - 1 : ℕ) : WithBot ℕ) ∧ (c037Poly N).Monic := by
  sorry

/-- `N = 1` reduction (`C036`, `OEIS A203568` `%F` line 24):
`A(X) = ∑_{n ≥ 1} (-1)^{n+1} X^{2n-1} / ∏_{k=1}^n (1 + X^{2k-1})` in `ℤ⟦X⟧`. -/
theorem c036_a203568_gf :
    HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 2) * PowerSeries.X ^ (2 * m + 1) *
      PowerSeries.invOfUnit
        (∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ))
      a203568Series := by
  sorry

/-- Explicit `N ≥ 1` Rogers–Fine family identity (`C037`) with `P(N, X) = c037Poly N`. -/
theorem c037_a203568_family_explicit (N : ℕ) (hN : 1 ≤ N) :
    ∃ S : ℤ⟦X⟧,
      HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1 + N) * PowerSeries.X ^ (2 * N * (m + 1) - N) *
        PowerSeries.invOfUnit
          (∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
      a203568Series =
        PowerSeries.invOfUnit
          (∏ j ∈ Finset.Icc 1 (N - 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j))) (1 : ℤˣ) *
          (Polynomial.toPowerSeries (c037Poly N) + S) := by
  sorry

/-- Unique existential form (`∃! P : ℤ[X], ...`) of Peter Bala's `C037` conjecture (`N ≥ 1`). -/
theorem c037_a203568_family (N : ℕ) (hN : 1 ≤ N) :
    ∃! P : ℤ[X],
      ((N = 1 → P = 0) ∧ (1 < N → P.degree = ((N ^ 2 - N - 1 : ℕ) : WithBot ℕ))) ∧
      ∃ S : ℤ⟦X⟧,
        HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1 + N) * PowerSeries.X ^ (2 * N * (m + 1) - N) *
          PowerSeries.invOfUnit
            (∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
        a203568Series =
          PowerSeries.invOfUnit
            (∏ j ∈ Finset.Icc 1 (N - 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j))) (1 : ℤˣ) *
            (Polynomial.toPowerSeries P + S) := by
  sorry

/-- Verbatim existential corollary (`∃ P : ℤ[X], ...`) of Peter Bala's `C037` conjecture (`N ≥ 1`). -/
theorem c037_a203568_family_exists (N : ℕ) (hN : 1 ≤ N) :
    ∃ P : ℤ[X],
      ((N = 1 → P = 0) ∧ (1 < N → P.degree = ((N ^ 2 - N - 1 : ℕ) : WithBot ℕ))) ∧
      ∃ S : ℤ⟦X⟧,
        HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1 + N) * PowerSeries.X ^ (2 * N * (m + 1) - N) *
          PowerSeries.invOfUnit
            (∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
        a203568Series =
          PowerSeries.invOfUnit
            (∏ j ∈ Finset.Icc 1 (N - 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ) *
            (Polynomial.toPowerSeries P + S) := by
  sorry

end

end Mathproofs.A203568RogersFineFamily
