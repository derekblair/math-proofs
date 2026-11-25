import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Seam B Entry C057 (OEIS A266437): Frozen Statement File

Verbatim transcription of the definitions and four theorem signatures from the frozen
pin manifest `PIN-C057.md` v1 (`sha256: fd1ba2551dcd430f6745e899ae570414a2f12060f958a0b5ae1dc2d7c8bd8378`,
`delta_vs_source: NONE`), materialized in the live Seam B layout
`MathProofs/SeamB/C057/Statement.lean` (path deviation from `PIN-C057.md`'s pre-Seam-B
target `Mathproofs/A266437Rule23On.lean` recorded in `VERIFICATION.md`).

All proofs live in `MathProofs/SeamB/C057/Solution.lean` with zero `sorry`.
-/

namespace A266437

def rule23 (l c r : Bool) : Bool :=
  (!l && !c && !r) || (!l && !c && r) || (!l && c && !r) || (l && !c && !r)

def ca : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule23 (ca n (j - 1)) (ca n j) (ca n (j + 1))

def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j = true)).card

theorem a_zero : a 0 = 1 := by
  sorry

theorem a_closed_form (n : ℕ) (hn : n > 0) :
    (a n : ℤ) * 2 = (1 - (-1 : ℤ) ^ n) * (2 * (n : ℤ) + 1) := by
  sorry

theorem a_recurrence (n : ℕ) (hn : n > 4) :
    (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  sorry

theorem a_gf :
    ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ) *
        PowerSeries.mk (fun n => (a n : ℚ)) =
      1 + 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + PowerSeries.X ^ 4 := by
  sorry

end A266437
