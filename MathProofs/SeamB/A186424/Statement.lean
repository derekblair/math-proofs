import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Seam B Entry A186424 (OEIS A186424): Frozen Statement File

Verbatim transcription of the definitions and theorem signatures from the frozen
pin manifest `PIN-A186424.md` v1
(`sha256: f6ae3e2474f1dc176d46947879978a778ee914d8178a2acce70cab83860d7757`,
single adjudicated `N = 0` boundary correction `Q_0 = 1`, zero delta for all `N ≥ 1`),
materialized in the live Seam B layout `MathProofs/SeamB/A186424/Statement.lean`
(path deviation from `PIN-A186424.md`'s pre-Seam-B target `Mathproofs/A186424.lean`
recorded in `VERIFICATION.md`, while preserving `namespace Mathproofs.A186424` and every
definition and theorem signature verbatim).

All proofs live in `MathProofs/SeamB/A186424/Solution.lean` with zero `sorry`.
-/

namespace Mathproofs.A186424

open scoped BigOperators Classical Polynomial PowerSeries PowerSeries.WithPiTopology

noncomputable section

/-- Primary `%N` `OEIS A186421` sequence (even numbers interleaved with repeated odd numbers,
offset `0`). -/
def a186421 (n : ℕ) : ℕ :=
  if Even n then n else 2 * (n / 4) + 1

/-- Primary `%N` `OEIS A186423` sequence (partial sums of `A186421`, offset `0`). -/
def a186423 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), a186421 i

/-- Primary `%N` `OEIS A186424` sequence (odd terms in `A186423` in order, offset `0`). -/
def a186424 (n : ℕ) : ℕ :=
  a186423 (Nat.nth (fun j ↦ Odd (a186423 j)) n)

/-- Explicit quadratic evaluation and strict monotonicity of `A186424`. -/
theorem a186424_closed_form :
    StrictMono a186424 ∧
      ∀ r : ℕ,
        a186424 (2 * r) = 6 * r ^ 2 + 4 * r + 1 ∧
        a186424 (2 * r + 1) = 6 * r ^ 2 + 8 * r + 3 := by
  sorry

/-- Formal power series `F(X) = 1 - X - X^3 + X^11 + X^17 - X^33 - X^43 + ...` in `ℤ⟦X⟧`
defined directly from `a186424`. -/
def a186424FalseTheta : ℤ⟦X⟧ :=
  PowerSeries.mk fun d ↦
    if d = 0 then 1
    else if h : ∃ m : ℕ, a186424 m = d then (-1 : ℤ) ^ (h.choose / 2 + 1)
    else 0

/-- Bala's base false-theta identity (`OEIS A186424` `%F` lines 21–22) under
`PowerSeries.WithPiTopology` (discrete topology on `ℤ`). -/
theorem a186424_base_series :
    HasSum (fun n : ℕ ↦ (-1 : ℤ⟦X⟧) ^ n * PowerSeries.X ^ n *
      PowerSeries.invOfUnit
        (∏ k ∈ Finset.Icc 1 n, (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ))
      a186424FalseTheta := by
  sorry

/-- Explicit polynomial family `Q_N(X) ∈ ℤ[X]` pinned for all `N : ℕ` by `Q_0(X) = 1` and
`Q_{N+1}(X) = (1 + X^(2N+1)) * Q_N(X) - X^(N+1)`. -/
def a186424Poly : ℕ → ℤ[X]
  | 0 => 1
  | N + 1 => (1 + Polynomial.X ^ (2 * N + 1)) * a186424Poly N - Polynomial.X ^ (N + 1)

/-- Closed-form product-and-sum formula for `a186424Poly N` (`∀ N : ℕ`). -/
theorem a186424Poly_closed_form (N : ℕ) :
    a186424Poly N =
      (∏ j ∈ Finset.Icc 1 N, (1 + (Polynomial.X : ℤ[X]) ^ (2 * j - 1))) -
        ∑ m ∈ Finset.Icc 1 N,
          (Polynomial.X : ℤ[X]) ^ m *
            ∏ j ∈ Finset.Icc (m + 1) N, (1 + (Polynomial.X : ℤ[X]) ^ (2 * j - 1)) := by
  sorry

/-- Adjudicated `N = 0` boundary and verbatim match to `OEIS A186424` empirical polynomials
for `N = 1..4`. -/
theorem a186424Poly_empirical_values :
    a186424Poly 0 = 1 ∧
      a186424Poly 1 = 1 ∧
      a186424Poly 2 = 1 - Polynomial.X ^ 2 + Polynomial.X ^ 3 ∧
      a186424Poly 3 =
        1 - Polynomial.X ^ 2 + Polynomial.X ^ 5 - Polynomial.X ^ 7 + Polynomial.X ^ 8 ∧
      a186424Poly 4 =
        1 - Polynomial.X ^ 2 - Polynomial.X ^ 4 + Polynomial.X ^ 5 + Polynomial.X ^ 8 -
          Polynomial.X ^ 9 + Polynomial.X ^ 12 - Polynomial.X ^ 14 + Polynomial.X ^ 15 := by
  sorry

/-- Exact degree, monicity, and constant term of `a186424Poly N`. -/
theorem a186424Poly_degree_and_monic :
    (a186424Poly 0).degree = (0 : WithBot ℕ) ∧
      (a186424Poly 0).Monic ∧
      ∀ N : ℕ, 1 ≤ N →
        (a186424Poly N).degree = ((N ^ 2 - 1 : ℕ) : WithBot ℕ) ∧
          (a186424Poly N).Monic ∧
          (a186424Poly N).coeff 0 = 1 := by
  sorry

/-- Explicit `N ≥ 0` family identity with `P(N, X) = a186424Poly N`. -/
theorem a186424_family_explicit (N : ℕ) :
    ∃ S : ℤ⟦X⟧,
      HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1) *
        PowerSeries.X ^ ((2 * N + 1) * (m + 1) - N) *
        PowerSeries.invOfUnit
          (∏ k ∈ Finset.Icc 1 (m + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
      PowerSeries.invOfUnit
        (∏ j ∈ Finset.Icc 1 N, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j - 1))) (1 : ℤˣ) *
        (Polynomial.toPowerSeries (a186424Poly N) + S) = a186424FalseTheta := by
  sorry

/-- Unique-polynomial existential form (`∃! P : ℤ[X], ...`) of Peter Bala's `A186424` family
(`∀ N : ℕ`). -/
theorem a186424_family (N : ℕ) :
    ∃! P : ℤ[X],
      ((N = 0 → P = 1) ∧ (1 ≤ N → P.degree = ((N ^ 2 - 1 : ℕ) : WithBot ℕ))) ∧
      ∃ S : ℤ⟦X⟧,
        HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1) *
          PowerSeries.X ^ ((2 * N + 1) * (m + 1) - N) *
          PowerSeries.invOfUnit
            (∏ k ∈ Finset.Icc 1 (m + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
        PowerSeries.invOfUnit
          (∏ j ∈ Finset.Icc 1 N, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j - 1))) (1 : ℤˣ) *
          (Polynomial.toPowerSeries P + S) = a186424FalseTheta := by
  sorry

/-- Immediate existential corollary (`∃ P : ℤ[X], ...`) of `a186424_family`. -/
theorem a186424_family_exists (N : ℕ) :
    ∃ P : ℤ[X],
      ((N = 0 → P = 1) ∧ (1 ≤ N → P.degree = ((N ^ 2 - 1 : ℕ) : WithBot ℕ))) ∧
      ∃ S : ℤ⟦X⟧,
        HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1) *
          PowerSeries.X ^ ((2 * N + 1) * (m + 1) - N) *
          PowerSeries.invOfUnit
            (∏ k ∈ Finset.Icc 1 (m + 1), (1 - (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
        PowerSeries.invOfUnit
          (∏ j ∈ Finset.Icc 1 N, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j - 1))) (1 : ℤˣ) *
          (Polynomial.toPowerSeries P + S) = a186424FalseTheta := by
  sorry

end

end Mathproofs.A186424
