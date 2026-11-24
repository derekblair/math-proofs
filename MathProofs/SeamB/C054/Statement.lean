import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-!
# Seam B Entry C054 (OEIS A266258): Frozen Statement File

Verbatim transcription of the definitions and six theorem signatures from the frozen
pin manifest `PIN-C054.md` v1
(`sha256: 93a607c738a4c5d08bb5c139179fadc8b8ef04a68061eac8599b1283d85fa5a0`,
embedded specification block `sha256: 98d9e8e57842c272fc2f356041bd5e50df95e46100fd741d1eb81ead8e0b43c8`,
`delta_vs_source: NONE`), materialized in the live Seam B layout
`MathProofs/SeamB/C054/Statement.lean` (path deviation from `PIN-C054.md`'s pre-Seam-B
target `Mathproofs/ECARule11OffC054.lean` recorded in `VERIFICATION.md`, while preserving
`namespace Mathproofs.ECARule11OffC054` and every definition and theorem signature verbatim).

All proofs live in `MathProofs/SeamB/C054/Solution.lean` with zero `sorry`.
-/

namespace Mathproofs.ECARule11OffC054

/-- Elementary Cellular Automaton Rule 11 (`11 = 0b00001011 = 2^3 + 2^1 + 2^0`):
maps neighborhood `(l, c, r)` (`true` = ON/black = `1`, `false` = OFF/white = `0`)
to bit `4*l + 2*c + r` of `11`. -/
def rule11 (l c r : Bool) : Bool :=
  match l, c, r with
  | true,  true,  true  => false
  | true,  true,  false => false
  | true,  false, true  => false
  | true,  false, false => false
  | false, true,  true  => true
  | false, true,  false => false
  | false, false, true  => true
  | false, false, false => true

/-- Bi-infinite evolution of ECA Rule 11 on all of `ℤ` starting from a single ON (`true`)
cell at `j = 0` and OFF (`false`) cells at all `j ≠ 0`. -/
def ca : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule11 (ca n (j - 1)) (ca n j) (ca n (j + 1))

/-- `A266258(n)`: number of OFF (`false` / white) cells in the active light-cone window
`[-n, n]` (`2n + 1` cells) at generation `n` of ECA Rule 11. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j : ℤ => ca n j = false)).card

/-- Explicit initial value at `n = 0` (outside the `n > 0` closed-form guard). -/
theorem a266258_zero : a 0 = 0 := by
  sorry

/-- Colin Barker's closed form for `A266258(n)` for `n > 0`. -/
theorem a266258_closed_form (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) =
      (2 * (-1 : ℚ) ^ n * (n : ℚ) + 2 * (n : ℚ) - 3 * (-1 : ℚ) ^ n + 1) / 2 := by
  sorry

/-- Colin Barker's 4-step linear recurrence for `A266258(n)` for `n > 4`. -/
theorem a266258_recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  sorry

/-- Colin Barker's rational ordinary generating function for `A266258` in `PowerSeries ℚ`
(cleared-denominator polynomial form). -/
theorem a266258_gf :
    ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
        (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) *
      PowerSeries.mk (fun n => (a n : ℚ)) =
    (PowerSeries.X : PowerSeries ℚ) *
      (2 + 3 * (PowerSeries.X : PowerSeries ℚ) -
        2 * (PowerSeries.X : PowerSeries ℚ) ^ 2 +
        (PowerSeries.X : PowerSeries ℚ) ^ 3) := by
  sorry

/-- Colin Barker's rational ordinary generating function for `A266258` in `PowerSeries ℚ`
(explicit unit-inverse quotient form via `PowerSeries.inv`). -/
theorem a266258_gf_inv :
    PowerSeries.mk (fun n => (a n : ℚ)) =
      ((PowerSeries.X : PowerSeries ℚ) *
        (2 + 3 * (PowerSeries.X : PowerSeries ℚ) -
          2 * (PowerSeries.X : PowerSeries ℚ) ^ 2 +
          (PowerSeries.X : PowerSeries ℚ) ^ 3)) *
      ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
        (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2)⁻¹ := by
  sorry

/-- Full bundled `C054` (`A266258`) statement combining `a(0) = 0`, the `n > 0` closed form,
the `n > 4` recurrence, and the `PowerSeries ℚ` generating-function identity. -/
theorem c054_a266258_bundle :
    a 0 = 0 ∧
    (∀ n : ℕ, 0 < n →
      (a n : ℚ) =
        (2 * (-1 : ℚ) ^ n * (n : ℚ) + 2 * (n : ℚ) - 3 * (-1 : ℚ) ^ n + 1) / 2) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
    ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
        (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) *
      PowerSeries.mk (fun n => (a n : ℚ)) =
    (PowerSeries.X : PowerSeries ℚ) *
      (2 + 3 * (PowerSeries.X : PowerSeries ℚ) -
        2 * (PowerSeries.X : PowerSeries ℚ) ^ 2 +
        (PowerSeries.X : PowerSeries ℚ) ^ 3) := by
  sorry

end Mathproofs.ECARule11OffC054
