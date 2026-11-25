import Mathlib

open scoped BigOperators

namespace MathProofs.SeamB.C042

/-! ### 1. Auxiliary Sequence 1: Square Array `A192062` (`S`) -/

/-- OEIS A192062 (`S(m, j)`): square array defined columnwise by
`S(0, j) = 0`, `S(1, j) = 1`, `S(2i, j) = S(2i-2, j) + S(2i-1, j)` (`i ≥ 1`),
and `S(2i+1, j) = S(2i-1, j) + j * S(2i, j)` (`i ≥ 1`). -/
def a192062 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, _ => 1
  | m + 2, j =>
    if (m + 2) % 2 = 0 then
      a192062 m j + a192062 (m + 1) j
    else
      a192062 m j + j * a192062 (m + 1) j

/-! ### 2. Primary Target Triangle: `A191579` (`R`) and Projections -/

/-- Connection-coefficient specification for the 0-indexed `n`-th row of `A191579`,
zero-extended for `k > n`, satisfying `S(2n+2, j+1) = ∑_{k=0..n} r(k) * S(2k+2, j)`
for every `j : ℕ` (corresponding to `j_orig = j + 1 ≥ 1` in `A191579` `%F`). -/
def IsA191579Row (n : ℕ) (r : ℕ → ℕ) : Prop :=
  (∀ k : ℕ, n < k → r k = 0) ∧
  ∀ j : ℕ, a192062 (2 * n + 2) (j + 1) =
    ∑ k ∈ Finset.range (n + 1), r k * a192062 (2 * k + 2) j

/-- OEIS A191579 (`R(n, k)`), 0-indexed (`0 ≤ k ≤ n`, zero-extended for `k > n`). -/
noncomputable def a191579 (n k : ℕ) : ℕ :=
  Classical.epsilon (IsA191579Row n) k

/-- Row-sum projection `∑_{k=0..n} R(n, k)` of `A191579`. -/
noncomputable def a191579RowSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), a191579 n k

/-- Column projection `n ↦ R(n, k)` of `A191579` (`k = 0, 1, 2, ...`). -/
noncomputable def a191579Col (k n : ℕ) : ℕ :=
  a191579 n k

/-! ### 3. Auxiliary Sequences 2–6: Peakless Motzkin Paths & Convolutions -/

/-- Step alphabet for Motzkin lattice paths: up `(1, 1)`, level `(1, 0)`, down `(1, -1)`. -/
inductive MotzkinStep : Type
  | U
  | H
  | D
  deriving DecidableEq

/-- Vertical step displacement in `ℤ`. -/
def MotzkinStep.delta : MotzkinStep → ℤ
  | .U => 1
  | .H => 0
  | .D => -1

/-- A Motzkin word is peakless if no `U` step is immediately followed by a `D` step. -/
def IsPeakless : List MotzkinStep → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => (x = .U → y ≠ .D) ∧ IsPeakless (y :: xs)

/-- Height after the first `i` steps of `w` (`prefixHeight w 0 = 0`). -/
def prefixHeight (w : List MotzkinStep) (i : ℕ) : ℤ :=
  ((w.take i).map MotzkinStep.delta).sum

/-- A peakless nonnegative Motzkin prefix (left factor of a peakless Motzkin path):
never goes below the x-axis (`0 ≤ prefixHeight w i` for all `i ≤ w.length`) and has no `UD` peak. -/
def IsPeaklessPrefix (w : List MotzkinStep) : Prop :=
  (∀ i : ℕ, i ≤ w.length → 0 ≤ prefixHeight w i) ∧ IsPeakless w

/-- Auxiliary Sequence 2 — OEIS A091964: number of left factors (prefixes) of peakless
Motzkin paths of length `n`. -/
noncomputable def a091964 (n : ℕ) : ℕ :=
  Nat.card {w : List MotzkinStep // w.length = n ∧ IsPeaklessPrefix w}

/-- Auxiliary Sequence 3 — OEIS A004148: number of peakless Motzkin excursions of length `n`
(RNA secondary structure numbers). -/
noncomputable def a004148 (n : ℕ) : ℕ :=
  Nat.card {w : List MotzkinStep // w.length = n ∧ IsPeaklessPrefix w ∧ prefixHeight w n = 0}

/-- Auxiliary Sequence 4 — OEIS A089735: self-convolution (2-fold Cauchy product) of `A004148`. -/
noncomputable def a089735 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), a004148 k * a004148 (n - k)

/-- Auxiliary Sequence 5 — OEIS A098075: threefold convolution of `A004148` with itself. -/
noncomputable def a098075 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1),
    a004148 i * a004148 j * a004148 (n - i - j)

/-- Auxiliary Sequence 6 — OEIS A097724: Riordan companion triangle counting peakless nonnegative
Motzkin prefixes of length `n` and endpoint height `k`. -/
noncomputable def a097724 (n k : ℕ) : ℕ :=
  Nat.card {w : List MotzkinStep // w.length = n ∧ IsPeaklessPrefix w ∧ prefixHeight w n = (k : ℤ)}

/-! ### 4. Pinned Theorems (Well-Definedness + Four-Claim C042 Bundle) -/

theorem a191579_row_exists_unique (n : ℕ) :
    ∃! r : ℕ → ℕ, IsA191579Row n r := by
  sorry

theorem a191579_rowSum_eq_a091964 (n : ℕ) :
    a191579RowSum n = a091964 n := by
  sorry

theorem a191579_col0_eq_a004148 (n : ℕ) :
    a191579Col 0 n = a004148 n := by
  sorry

theorem a191579_col1_eq_a089735 (n : ℕ) (hn : 1 ≤ n) :
    a191579Col 1 n = a089735 (n - 1) := by
  sorry

theorem a191579_col2_eq_a098075 (n : ℕ) (hn : 2 ≤ n) :
    a191579Col 2 n = a098075 (n - 2) := by
  sorry

end MathProofs.SeamB.C042
