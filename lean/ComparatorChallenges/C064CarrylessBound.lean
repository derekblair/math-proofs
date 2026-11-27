import Mathlib

/-!
# C064 — Carryless Binary Product Quotient Bound (OEIS A115861 / A391736)

Standalone Mathlib-only comparator challenge file pinning the refutation of
Antti Karttunen's conjecture on OEIS `A391736` / `A115861` (`PIN-C064.md` v1):

- `A048720(a, b)` is carryless base-2 multiplication (`clMul a b`), corresponding
  to polynomial multiplication over `GF(2)[X]` encoded in binary.
- `A115861(n)` counts integers `m` in `1 .. n - 1` for which there exists
  `i` in `1 .. n ^ 3` satisfying `m * i = clMul n i`.
- Row `n` of `A391736` consists of all quotients `m = clMul n i / i` over odd `i ≥ 1`
  dividing `clMul n i`.
- Conjecture (`A391736` `%C`): `1 + A115861(n)` is the exact number of distinct
  values occurring on row `n` of `A391736` (equivalently, no new quotient `m < n`
  first appears at `i > n ^ 3`).
- Related formula (`A115861` `%F`): `A115861(2 * n) = A115861(n)` for all `n ≥ 1`.

All proofs live in `MathProofs.SeamB.C064.Solution` with zero `sorry` and standard
axioms only (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace C064

/-- Carryless base-2 multiplication (`OEIS A048720`), corresponding to polynomial
multiplication in `GF(2)[X]` encoded in binary:
`clMul a 0 = 0`, `clMul a (2 * k) = 2 * clMul a k`, and
`clMul a (2 * k + 1) = (2 * clMul a k) ^^^ a`. -/
def clMul (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else
    let half := clMul a (b / 2)
    if b % 2 = 1 then (2 * half) ^^^ a else 2 * half

/-- The set of distinct values occurring on row `n` of `OEIS A391736`: all integers `m`
such that `m * i = A048720(n, i)` for some odd integer `i ≥ 1`. -/
def rowA391736Values (n : ℕ) : Set ℕ :=
  { m : ℕ | ∃ i : ℕ, 0 < i ∧ i % 2 = 1 ∧ m * i = clMul n i }

/-- The finite set of integers `m ∈ {1, ..., n - 1}` admitting a solution
`m * i = A048720(n, i)` with `1 ≤ i ≤ n ^ 3`. -/
def A115861_set (n : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 n).filter (fun m =>
    ((Finset.Icc 1 (n ^ 3)).filter (fun i => m * i = clMul n i)).Nonempty)

/-- `OEIS A115861(n)`: number of integers `m` in `1 .. n - 1` for which there exists
`i` in `1 .. n ^ 3` such that `m * i = A048720(n, i)`. -/
def A115861 (n : ℕ) : ℕ :=
  (A115861_set n).card

/-- Minimal counterexample witness `(n, m, i) = (239, 215, 302775165)`:
`215 * 302775165 = A048720(239, 302775165) = 65096660475` with `302775165 > 239 ^ 3 = 13651919`,
while NO integer `i` in `1 .. 239 ^ 3` satisfies `215 * i = A048720(239, i)`. -/
theorem c064_witness :
    1 ≤ 215 ∧ 215 < 239 ∧ 239 ^ 3 < 302775165 ∧ 302775165 % 2 = 1 ∧
    215 * 302775165 = clMul 239 302775165 ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 239 ^ 3 → 215 * i ≠ clMul 239 i) := by
  sorry

/-- Formal refutation of `OEIS A391736` `%C`: `1 + A115861(n)` is NOT in general equal to
the exact number of distinct values occurring on row `n` of `A391736` (fails at `n = 239`,
where `1 + A115861(239) = 4 < 5 = (rowA391736Values 239).ncard`). -/
theorem c064_refutation_card :
    ¬ (∀ n : ℕ, 1 ≤ n → (rowA391736Values n).ncard = 1 + A115861 n) := by
  sorry

/-- Pointwise refutation of the `n ^ 3` search-bound sufficiency conjecture:
there exist `n ≥ 1` and `1 ≤ m < n` occurring on row `n` of `A391736` with NO witness
`i ∈ {1, ..., n ^ 3}`. -/
theorem c064_refutation_pointwise :
    ¬ (∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, 1 ≤ m → m < n →
      m ∈ rowA391736Values n → ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ^ 3 ∧ m * i = clMul n i) := by
  sorry

/-- Corollary refuting `OEIS A115861` `%F` (`a(2 * n) = a(n)` for all `n ≥ 1`) under the
published `n ^ 3`-truncated definition: fails at `n = 478`, where `A115861(478) < A115861(956)`. -/
theorem c064_refutation_doubling :
    ¬ (∀ n : ℕ, 1 ≤ n → A115861 (2 * n) = A115861 n) := by
  sorry

end C064
