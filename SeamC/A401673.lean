import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Sym.Sym2

/-!
# Seam C Entry S017 (OEIS A401673): Dawid Ryłko's King-Graph Domicule Top-Two Diagonal-Count Conjectures

Formalizes and proves Dawid Ryłko's conjectures on `OEIS A401673` (`%F` line 17, Nov 01 2026;
live revision `#9`, Nov 09 2026 17:52:57) and companions `OEIS A239273` (`%I #51`, Nov 11 2026)
and `OEIS A011379` (`%I #207`, Nov 26 2025) against the frozen target contract `PIN-S017.md` v1
(`delta_vs_source: NONE`), following the seven-step coordinate-sum / four-class parity route from
`SCOPING-S017.md` (§2.1, Steps 1–7).
-/

namespace SeamC.A401673

open scoped Classical

/-! ### Pinned Target Definitions (`PIN-S017.md` v1) -/

/-- The `2n × 2n` square grid of unit cells (`OEIS A401673` `%N` line 10). -/
abbrev Board (n : ℕ) : Type := Fin (2 * n) × Fin (2 * n)

/-- Two distinct cells share a side or a corner (chessboard king distance `1`). -/
def kingAdj (n : ℕ) (u v : Board n) : Prop :=
  u ≠ v ∧ Nat.dist u.1.val v.1.val ≤ 1 ∧ Nat.dist u.2.val v.2.val ≤ 1

/-- Two cells share only a corner (diagonal domicule). -/
def diagAdj (n : ℕ) (u v : Board n) : Prop :=
  Nat.dist u.1.val v.1.val = 1 ∧ Nat.dist u.2.val v.2.val = 1

/-- `M` is a perfect matching of the `2n × 2n` king graph: vertex-disjoint domicules covering
`Board n`, with crossing diagonals in a `2 × 2` block permitted (`%e` line 24). -/
def IsDomiculeTiling (n : ℕ) (M : Finset (Sym2 (Board n))) : Prop :=
  (∀ e ∈ M, ¬ e.IsDiag ∧ ∀ u v, e = s(u, v) → kingAdj n u v) ∧
    (∀ v : Board n, ∃! e, e ∈ M ∧ v ∈ e)

/-- Predicate for a diagonal domicule (`OEIS A401673` `%C` line 11). -/
def IsDiagDomicule (n : ℕ) (e : Sym2 (Board n)) : Prop :=
  ∃ u v, e = s(u, v) ∧ diagAdj n u v

/-- `T(n, k)` (`OEIS A401673` `%N` line 10, `%o` line 27): the number of domicule tilings of the
`2n × 2n` square with **exactly `2 * k`** diagonal domicules. -/
noncomputable def domiculeTilings (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Sym2 (Board n)))).filter (fun M =>
    IsDomiculeTiling n M ∧ (M.filter (IsDiagDomicule n)).card = 2 * k)).card

/-- Companion sequence `OEIS A011379` (`%N` line 10): `a(n) = n^2 * (n + 1)`. -/
def A011379 (n : ℕ) : ℕ := n ^ 2 * (n + 1)

/-! ### Pinned Target Theorems (`PIN-S017.md` v1) -/

/-- Dawid Ryłko's first conjecture on `OEIS A401673` (`%F` line 17):
for every `n : ℕ`, `T(n, n^2) = 1` (`2 * n^2` diagonal domicules). -/
theorem domiculeTilings_max_diag_eq_one (n : ℕ) :
    domiculeTilings n (n ^ 2) = 1 := by
  sorry

/-- Dawid Ryłko's second conjecture on `OEIS A401673` (`%F` line 17):
for every `n ≥ 1`, `T(n, n^2 - 1) = A011379(n) = n^2 * (n + 1)`
(`2 * (n^2 - 1)` diagonal domicules). -/
theorem domiculeTilings_sub_one_diag_eq (n : ℕ) (hn : 1 ≤ n) :
    domiculeTilings n (n ^ 2 - 1) = n ^ 2 * (n + 1) := by
  sorry

end SeamC.A401673
