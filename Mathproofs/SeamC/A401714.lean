import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Lattice.Nat

/-!
# Seam C `S010` (`OEIS A401714 ≤ A401715`): Karttunen's Unitary/Squarefree Divisor Inequality

Statement contract frozen from `PIN-S010.md` v1 (`delta_vs_source: NONE`) for Antti Karttunen's
Nov 06 2026 conjecture on `OEIS A401714` (`%F` lines 13–14, rev `#12`) and `OEIS A401715`
(`%F` line 15, rev `#13`).
-/

namespace SeamC.A401714

/-- `OEIS A007947`: Squarefree kernel `rad(n)`, product of distinct prime factors `p` in
`n.primeFactors` (`rad 1 = 1`). -/
def rad (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

/-- `OEIS A003557`: `n` divided by its squarefree kernel `rad(n)` (`a003557 1 = 1`). -/
def a003557 (n : ℕ) : ℕ :=
  n / rad n

/-- `OEIS A053669`: Smallest prime `p` not dividing `n` (`a053669 1 = 2`, `a053669 0 = 0`). -/
noncomputable def a053669 (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ ¬ p ∣ n}

/-- `OEIS A034448`: Sum of unitary divisors of `n` (`d ∈ n.divisors` with `Nat.Coprime d (n / d)`;
`a034448 1 = 1`). -/
def a034448 (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors with Nat.Coprime d (n / d), d

/-- `OEIS A048250`: Sum of squarefree divisors of `n` (`d ∈ n.divisors` with `Squarefree d`;
`a048250 1 = 1`). -/
def a048250 (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors with Squarefree d, d

/-- `OEIS A401714`: `{0,1}`-valued Iverson indicator `if a003557 n < a053669 n then 1 else 0`
(`a401714 1 = 1`). -/
noncomputable def a401714 (n : ℕ) : ℕ :=
  if a003557 n < a053669 n then 1 else 0

/-- `OEIS A401715`: `{0,1}`-valued Iverson indicator
`if 2 * n ≤ a034448 n + a048250 n then 1 else 0` (`a401715 1 = 1`). -/
def a401715 (n : ℕ) : ℕ :=
  if 2 * n ≤ a034448 n + a048250 n then 1 else 0

/-- Canonical form (`PIN-S010.md` v1): for all `n : ℕ`, `1 ≤ n → a401714 n ≤ a401715 n`. -/
theorem a401714_le_a401715 :
    ∀ n : ℕ, 1 ≤ n → a401714 n ≤ a401715 n := by
  sorry

/-- Equivalent implication form (`PIN-S010.md` v1): for all `n : ℕ`,
`1 ≤ n → a003557 n < a053669 n → 2 * n ≤ a034448 n + a048250 n`. -/
theorem a401714_imp_a401715 :
    ∀ n : ℕ, 1 ≤ n → a003557 n < a053669 n → 2 * n ≤ a034448 n + a048250 n := by
  sorry

end SeamC.A401714
