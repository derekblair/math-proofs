import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat

/-!
# Seam C Entry S006 (OEIS A363166): Gómez Calderón's 3-Heap Nim Identity

Staged target contract from `PIN-S006.md` v1 (`delta_vs_source: NONE`) for Alan Michael Gómez
Calderón's conjectured formula on `OEIS A363166` (`%F` line 17, Sep 18 2025; live revision `#26`,
Sep 23 2025) and companion `OEIS A063915` (`%F` lines 17–18, Kevin Ryde, Nov 27 2020).
-/

namespace SeamC.A363166

/-- `OEIS A363166(n)` (for `n ≥ 1`): cardinality of the finite set of unordered nonzero heap
triples `((x, y), z)` in `((Finset.Icc 1 n ×ˢ Finset.Icc 1 n) ×ˢ Finset.Icc 1 n)` satisfying
`x ≤ y ∧ y ≤ z ∧ Nat.xor (Nat.xor x y) z = 0` (`nimTriples 1 = 0`). -/
def nimTriples (n : ℕ) : ℕ :=
  (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n) ×ˢ Finset.Icc 1 n).filter
    (fun ((x, y), z) => x ≤ y ∧ y ≤ z ∧ Nat.xor (Nat.xor x y) z = 0)).card

/-- Auxiliary binary recurrence `b(n)` from `OEIS A063915` (`%F` line 17, `%t` lines 23–25):
`a063915Aux 0 = 0`, `a063915Aux 1 = 1`, `a063915Aux (2 * k) = 2 * a063915Aux k +
2 * a063915Aux (k - 1) + 1` for `k ≥ 1`, and `a063915Aux (2 * k + 1) = 4 * a063915Aux k + 1`
for `k ≥ 1`. -/
def a063915Aux : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then
      2 * a063915Aux ((n + 2) / 2) + 2 * a063915Aux ((n + 2) / 2 - 1) + 1
    else
      4 * a063915Aux ((n + 2) / 2) + 1

/-- `OEIS A063915(m)`: `a063915 m = a063915Aux (m + 1)` (`a063915 0 = 1`, `a063915 1 = 3`,
`a063915 2 = 5`). -/
def a063915 (m : ℕ) : ℕ :=
  a063915Aux (m + 1)

/-- Primary theorem (`OEIS A363166` `%F` line 17, Alan Michael Gómez Calderón, Sep 18 2025):
for every `n : ℕ` with `1 ≤ n`, `nimTriples n + a063915 (n - 1) = n * (n + 1) / 2`. -/
theorem nim_triples_add_a063915_eq_triangular (n : ℕ) (hn : 1 ≤ n) :
    nimTriples n + a063915 (n - 1) = n * (n + 1) / 2 := by
  sorry

/-- Companion equivalence theorem (`OEIS A063915` `%F` line 18, Kevin Ryde, Nov 27 2020):
for every `m : ℕ`, letting `k = Nat.log 2 (m + 2)`,
`3 * a063915 m + (2 * 4 ^ k + 1) = 3 * (m + 2) * 2 ^ k` and
`a063915 m = (m + 2) * 2 ^ k - (2 * 4 ^ k + 1) / 3`. -/
theorem a063915_eq_closed_form (m : ℕ) :
    let k := Nat.log 2 (m + 2)
    3 * a063915 m + (2 * 4 ^ k + 1) = 3 * (m + 2) * 2 ^ k ∧
      a063915 m = (m + 2) * 2 ^ k - (2 * 4 ^ k + 1) / 3 := by
  sorry

/-- Closed-form corollary: for every `n : ℕ` with `1 ≤ n`, letting `k = Nat.log 2 (n + 1)`,
`nimTriples n + ((n + 1) * 2 ^ k - (2 * 4 ^ k + 1) / 3) = n * (n + 1) / 2`. -/
theorem nim_triples_add_closed_form_eq_triangular (n : ℕ) (hn : 1 ≤ n) :
    let k := Nat.log 2 (n + 1)
    nimTriples n + ((n + 1) * 2 ^ k - (2 * 4 ^ k + 1) / 3) = n * (n + 1) / 2 := by
  sorry

end SeamC.A363166
