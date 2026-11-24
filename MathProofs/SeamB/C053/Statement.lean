import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Seam B Entry C053 (OEIS A266662): Frozen Statement File

Verbatim transcription of the definitions and seven theorem signatures from the frozen
pin manifest `PIN-C053.md` v1
(`sha256: 8743cc387e9a8a91c21641408bf8ec20300f9cdc66484ef2324bf07815d5f056`,
`delta_vs_source: NONE`), materialized in the live Seam B layout
`MathProofs/SeamB/C053/Statement.lean` (path deviation from `PIN-C053.md`'s pre-Seam-B
target `Mathproofs/A266662.lean` recorded in `VERIFICATION.md`, while preserving
`namespace Mathproofs.A266662` and every definition and theorem signature verbatim).

All proofs live in `MathProofs/SeamB/C053/Solution.lean` with zero `sorry`.
-/

namespace Mathproofs.A266662

/-- Wolfram Rule 47 elementary cellular automaton local rule (`47 = 0b00101111`):
maps `(l, c, r)` to bit `4 * l.toNat + 2 * c.toNat + r.toNat` of `47`. -/
def rule47 (l c r : Bool) : Bool :=
  match l, c, r with
  | false, false, false => true
  | false, false, true  => true
  | false, true,  false => true
  | false, true,  true  => true
  | true,  false, false => false
  | true,  false, true  => true
  | true,  true,  false => false
  | true,  true,  true  => false

/-- Bi-infinite 1D evolution of Rule 47 on `ℤ` starting from a single ON (`true`) cell at `0`. -/
def ca : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule47 (ca n (j - 1)) (ca n j) (ca n (j + 1))

/-- OEIS A266662: number of ON (`true`) cells in the active light-cone window `[-n, n]` at step `n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j = true)).card

/-- Consistency of the explicit truth table with Wolfram bit-indexing of `47`. -/
theorem rule47_eq_testBit (l c r : Bool) :
    rule47 l c r = (47 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  sorry

/-- Initial value at `n = 0`: the single seed cell at `0` is ON. -/
theorem a_zero : a 0 = 1 := by
  sorry

/-- Initial value at `n = 1`: window `[-1, 1]` has bit profile `[true, true, false]`, giving `2`. -/
theorem a_one : a 1 = 2 := by
  sorry

/-- Colin Barker's closed form for `A266662(n)` for `n > 1`. -/
theorem a_closed_form (n : ℕ) (hn : 1 < n) :
    2 * (a n : ℤ) = -2 * (-1 : ℤ) ^ n * (n : ℤ) + 2 * (n : ℤ) + 3 * (-1 : ℤ) ^ n + 1 := by
  sorry

/-- Colin Barker's 4-step linear recurrence for `A266662(n)` for `n > 5`. -/
theorem a_recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  sorry

/-- Colin Barker's ordinary generating function for `A266662` in `PowerSeries ℚ`. -/
theorem a_gf :
    ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 * (1 + PowerSeries.X) ^ 2) *
      PowerSeries.mk (fun n => (a n : ℚ)) =
    1 + 2 * PowerSeries.X + PowerSeries.X ^ 3 - PowerSeries.X ^ 4 + PowerSeries.X ^ 5 := by
  sorry

/-- Full C053 target bundle combining initial values, closed form, recurrence, and g.f. -/
theorem c053_bundle :
    a 0 = 1 ∧
    a 1 = 2 ∧
    (∀ n : ℕ, 1 < n →
      2 * (a n : ℤ) = -2 * (-1 : ℤ) ^ n * (n : ℤ) + 2 * (n : ℤ) + 3 * (-1 : ℤ) ^ n + 1) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
    (((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 * (1 + PowerSeries.X) ^ 2) *
      PowerSeries.mk (fun n => (a n : ℚ)) =
      1 + 2 * PowerSeries.X + PowerSeries.X ^ 3 - PowerSeries.X ^ 4 + PowerSeries.X ^ 5) := by
  sorry

end Mathproofs.A266662
