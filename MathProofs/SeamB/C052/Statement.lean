import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Seam B Entry C052 (OEIS A266256): Frozen Statement File

Verbatim transcription of the definitions and six theorem signatures from the frozen
pin manifest `PIN-C052.md` v1
(`sha256: f6e0818fe636e3d52e04e4965d5750c5c7a169ebfe1229157a5a25d7efaf88c0`,
`delta_vs_source: NONE`), materialized in the live Seam B layout
`MathProofs/SeamB/C052/Statement.lean` (path deviation from `PIN-C052.md`'s pre-Seam-B
target `Mathproofs/A266256.lean` recorded in `VERIFICATION.md`, while preserving
`namespace Mathproofs.A266256` and every definition and theorem signature verbatim).

All proofs live in `MathProofs/SeamB/C052/Solution.lean` with zero `sorry`.
-/

namespace Mathproofs.A266256

/-- Wolfram Elementary Cellular Automaton Rule 11 (`11 = 0b00001011`):
explicit 8-branch truth table mapping `(false, false, false)`, `(false, false, true)`,
and `(false, true, true)` to `true` and the other five triples to `false`. -/
def rule11 (l c r : Bool) : Bool :=
  match l, c, r with
  | false, false, false => true
  | false, false, true  => true
  | false, true,  false => false
  | false, true,  true  => true
  | true,  false, false => false
  | true,  false, true  => false
  | true,  true,  false => false
  | true,  true,  true  => false

/-- Bi-infinite evolution of Rule 11 on `ℤ` starting from a single ON cell at `j = 0`. -/
def ca : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule11 (ca n (j - 1)) (ca n j) (ca n (j + 1))

/-- `A266256(n)`: number of ON (`true`) cells in the active window `[-n, n]` at generation `n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j = true)).card

-- Exact theorem signatures required in the solution closure (no `sorry` in closure):

theorem rule11_eq_testBit (l c r : Bool) :
    rule11 l c r = Nat.testBit 11 ((if l then 4 else 0) + (if c then 2 else 0) + (if r then 1 else 0)) := by
  sorry

theorem a_zero : a 0 = 1 := by
  sorry

theorem a_closed_form (n : ℕ) (hn : 0 < n) :
    2 * (a n : ℤ) = -2 * ((-1 : ℤ) ^ n - 1) * (n : ℤ) + 3 * (-1 : ℤ) ^ n + 1 := by
  sorry

theorem a_recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  sorry

theorem a_gf :
    ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 * (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) *
        PowerSeries.mk (fun n => (a n : ℚ)) =
      1 + (PowerSeries.X : PowerSeries ℚ) + 3 * (PowerSeries.X : PowerSeries ℚ) ^ 3 -
        (PowerSeries.X : PowerSeries ℚ) ^ 4 := by
  sorry

theorem c052_a266256_bundle :
    a 0 = 1 ∧
      (∀ n : ℕ, 0 < n → 2 * (a n : ℤ) = -2 * ((-1 : ℤ) ^ n - 1) * (n : ℤ) + 3 * (-1 : ℤ) ^ n + 1) ∧
      (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
      (((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 * (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) *
          PowerSeries.mk (fun n => (a n : ℚ)) =
        1 + (PowerSeries.X : PowerSeries ℚ) + 3 * (PowerSeries.X : PowerSeries ℚ) ^ 3 -
          (PowerSeries.X : PowerSeries ℚ) ^ 4) := by
  sorry

end Mathproofs.A266256
