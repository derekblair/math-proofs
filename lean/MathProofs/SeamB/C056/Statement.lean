import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Seam B Entry C056 (OEIS A266220): Frozen Statement File

Verbatim transcription of the definitions and six theorem signatures from the frozen
pin manifest `PIN-C056.md` v1 (`sha256: 8da44cf6be8b7ca7a58a12cbb59814efc55d899b48d77abc569887158b48691a`,
normalized self-SHA `e30c23cb5a19a810c68211cd478c8e10bb397d696db63efdf22a22f2749a8d67`,
`delta_vs_source: NONE`), materialized in the live Seam B layout
`MathProofs/SeamB/C056/Statement.lean` (path deviation from `PIN-C056.md`'s pre-Seam-B
target `Mathproofs/A266220.lean` recorded in `VERIFICATION.md`).

All proofs live in `MathProofs/SeamB/C056/Solution.lean` with zero `sorry`.
-/

namespace A266220

def rule7 (l c r : Bool) : Bool := (!l && !c) || (!l && c && !r)

def ca : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule7 (ca n (j - 1)) (ca n j) (ca n (j + 1))

def a (n : ℕ) : ℕ := ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j = true)).card

theorem a_zero : a 0 = 1 := by
  sorry

theorem a_one : a 1 = 2 := by
  sorry

theorem a_closed_form : ∀ n : ℕ, n > 1 → (a n : ℤ) * 2 = (1 - (-1 : ℤ) ^ n) * (2 * (n : ℤ) + 1) := by
  sorry

theorem a_recurrence : ∀ n : ℕ, n > 5 → (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  sorry

theorem a_gf : (((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ) * PowerSeries.mk (fun n => (a n : ℚ))) = (1 + 2 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + 3 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - PowerSeries.X ^ 5 : PowerSeries ℚ) := by
  sorry

theorem c056_bundle : (∀ n : ℕ, n > 1 → (a n : ℤ) * 2 = (1 - (-1 : ℤ) ^ n) * (2 * (n : ℤ) + 1)) ∧ (∀ n : ℕ, n > 5 → (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧ ((((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ) * PowerSeries.mk (fun n => (a n : ℚ))) = (1 + 2 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + 3 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - PowerSeries.X ^ 5 : PowerSeries ℚ)) := by
  sorry

end A266220
