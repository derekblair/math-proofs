import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.PowerSeries.Basic

namespace Mathproofs.A266439Rule23Off

/-- Wolfram Elementary Cellular Automaton Rule 23 (`23 = 0b00010111`):
maps `(l, c, r)` (`true` = ON/black, `false` = OFF/white) to bit `4*l + 2*c + r` of `23`. -/
def rule23 (l c r : Bool) : Bool :=
  Nat.testBit 23 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Full-lattice evolution of Rule 23 on `ℤ` starting from a single ON cell at `j = 0`. -/
def ca : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule23 (ca n (j - 1)) (ca n j) (ca n (j + 1))

/-- `A266439(n)`: number of OFF (`false`) cells in the active window `[-n, n]` at generation `n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca n j))).card

-- Exact theorem signatures required in the solution closure (no `sorry` in closure):

theorem rule23_truth_table (l c r : Bool) :
    rule23 l c r =
      match l, c, r with
      | false, false, false => true
      | false, false, true  => true
      | false, true,  false => true
      | true,  false, false => true
      | _,     _,     _     => false := by
  sorry

theorem a_zero : a 0 = 0 := by
  sorry

theorem a_closed_form (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = (((-1 : ℚ) ^ n + 1) * (2 * (n : ℚ) + 1)) / 2 := by
  sorry

theorem a_recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  sorry

theorem a_gf :
    ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
      (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) *
      PowerSeries.mk (fun n => (a n : ℚ)) =
    (PowerSeries.X : PowerSeries ℚ) ^ 2 *
      (5 - (PowerSeries.X : PowerSeries ℚ) ^ 2) := by
  sorry

theorem c051_a266439_bundle :
    a 0 = 0 ∧
    (∀ n : ℕ, 0 < n →
      (a n : ℚ) = (((-1 : ℚ) ^ n + 1) * (2 * (n : ℚ) + 1)) / 2) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
    (((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
        (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) *
        PowerSeries.mk (fun n => (a n : ℚ)) =
      (PowerSeries.X : PowerSeries ℚ) ^ 2 *
        (5 - (PowerSeries.X : PowerSeries ℚ) ^ 2)) := by
  sorry

end Mathproofs.A266439Rule23Off
