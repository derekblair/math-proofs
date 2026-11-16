import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Seam C Entry S012 (OEIS A401496): Mwafise's Complement-Closed Riordan-Graph Recurrence

Staged target contract from `PIN-S012.md` v1 (`delta_vs_source: NONE`) for Arnauld Mesinga Mwafise's
conjectured recurrence on `OEIS A401496` (`%F` line 12, Oct 27 2026; live revision `#9`,
Nov 04 2026 15:05:12) and `OEIS A401493` (`%C` line 10, live revision `#10`, Nov 03 2026 17:02:17).
-/

namespace SeamC.A401496

/-- Labeled Riordan graph predicate (`OEIS A401493` `%C` line 10, 0-based on `Fin n` via
`I = i.val + 1`, `J = j.val + 1`): `G` arises from formal power series `g, f` over `GF(2)`
(`ZMod 2`) with `f(0) = 0` such that for `0 ≤ j < i < n`, `G.Adj i j` holds iff
`[t^(i - 1)] (g(t) * f(t)^j) = 1`. -/
def IsLabeledRiordanGraph (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ g f : PowerSeries (ZMod 2), PowerSeries.coeff 0 f = 0 ∧
    ∀ i j : Fin n, j.val < i.val → (G.Adj i j ↔ PowerSeries.coeff (i.val - 1) (g * f ^ j.val) = 1)

/-- `OEIS A401496(n)` (`%N` line 8): number of labeled Riordan graphs of order `n` whose graph
complement `Gᶜ` on the same vertex labeling `Fin n` is also a labeled Riordan graph. -/
noncomputable def complementClosedRiordanCount (n : ℕ) : ℕ :=
  Nat.card { G : SimpleGraph (Fin n) // IsLabeledRiordanGraph n G ∧ IsLabeledRiordanGraph n Gᶜ }

/-- Base value at `n = 1` (`OEIS A401496` `%O 1,2`, `%S` line 7 first entry). -/
theorem complementClosed_riordan_count_one : complementClosedRiordanCount 1 = 1 := by
  sorry

/-- Base value at `n = 2` (`OEIS A401496` `%O 1,2`, `%S` line 7 second entry). -/
theorem complementClosed_riordan_count_two : complementClosedRiordanCount 2 = 2 := by
  sorry

/-- Main recurrence (`OEIS A401496` `%F` line 12, Arnauld Mesinga Mwafise, Oct 27 2026):
for every `n : ℕ` with `3 ≤ n`, `a(n) = 8 * a(n - 2) - 4`. -/
theorem complementClosed_riordan_count_eq (n : ℕ) (hn : 3 ≤ n) :
    complementClosedRiordanCount n = 8 * complementClosedRiordanCount (n - 2) - 4 := by
  sorry

end SeamC.A401496
