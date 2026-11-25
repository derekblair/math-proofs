import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Seam B Entry C055 (OEIS A266664): Frozen Statement File

Verbatim transcription of the definitions and seven theorem signatures from the frozen
pin manifest `PIN-C055.md` v1
(`sha256: 9a261730585d5000f09182e4980025ca1ae486554d384e340214e840a768f69e`,
`delta_vs_source: NONE`), materialized in the live Seam B layout
`MathProofs/SeamB/C055/Statement.lean` (path deviation from `PIN-C055.md`'s pre-Seam-B
target `Mathproofs/A266664.lean` recorded in `VERIFICATION.md`, while preserving
`namespace Mathproofs.A266664` and every definition and theorem signature verbatim).

All proofs live in `MathProofs/SeamB/C055/Solution.lean` with zero `sorry`.
-/

namespace Mathproofs.A266664

/-- Wolfram Rule 47 elementary cellular automaton local rule (`47 = 0b00101111`):
maps `(l, c, r)` to bit `4 * l.toNat + 2 * c.toNat + r.toNat` of `47`. -/
def rule47 (l c r : Bool) : Bool := (47 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Bi-infinite 1D evolution of Rule 47 on `ℤ` starting from a single ON (`true`) cell at `0`. -/
def ca : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule47 (ca n (j - 1)) (ca n j) (ca n (j + 1))

/-- OEIS A266664: number of OFF (`false` / white) cells in the active light-cone window
`[-n, n]` at generation `n`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca n j))).card

/-- Explicit 8-entry truth-table verification of `rule47` (`0b00101111`). -/
theorem rule47_truth_table :
    rule47 false false false = true ∧ rule47 false false true = true ∧
    rule47 false true false = true ∧ rule47 false true true = true ∧
    rule47 true false false = false ∧ rule47 true false true = true ∧
    rule47 true true false = false ∧ rule47 true true true = false := by
  sorry

/-- Pinned seed OFF-cell count at generation `n = 0`: `a 0 = 0`. -/
theorem a_zero : a 0 = 0 := by
  sorry

/-- Pinned OFF-cell count at generation `n = 1`: `a 1 = 1`. -/
theorem a_one : a 1 = 1 := by
  sorry

/-- Colin Barker's closed form for `A266664(n)` for `n > 1`. -/
theorem a_closed_form (n : ℕ) (hn : 1 < n) :
    (a n : ℚ) = (2 * (-1 : ℚ) ^ n * (n : ℚ) + 2 * (n : ℚ) - 3 * (-1 : ℚ) ^ n + 1) / 2 := by
  sorry

/-- Colin Barker's 4-step linear recurrence for `A266664(n)` for `n > 5`. -/
theorem a_recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  sorry

/-- Colin Barker's ordinary generating function for `A266664` in `PowerSeries ℚ`. -/
theorem a_gf :
    ((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 * (1 + PowerSeries.X : PowerSeries ℚ) ^ 2) *
      PowerSeries.mk (fun n => (a n : ℚ)) =
    (PowerSeries.X : PowerSeries ℚ) *
      (1 + 3 * PowerSeries.X + PowerSeries.X ^ 3 - PowerSeries.X ^ 4) := by
  sorry

/-- Full C055 target bundle combining initial values, closed form, recurrence, and g.f. -/
theorem c055_bundle :
    a 0 = 0 ∧
    a 1 = 1 ∧
    (∀ n : ℕ, 1 < n →
      (a n : ℚ) = (2 * (-1 : ℚ) ^ n * (n : ℚ) + 2 * (n : ℚ) - 3 * (-1 : ℚ) ^ n + 1) / 2) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
    (((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 * (1 + PowerSeries.X : PowerSeries ℚ) ^ 2) *
      PowerSeries.mk (fun n => (a n : ℚ)) =
      (PowerSeries.X : PowerSeries ℚ) *
        (1 + 3 * PowerSeries.X + PowerSeries.X ^ 3 - PowerSeries.X ^ 4)) := by
  sorry

end Mathproofs.A266664
