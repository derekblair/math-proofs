import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Fib.Zeckendorf

/-!
# Seam C `S003` (`OEIS A385590`): Fibonacci Triangle Bijection onto `ℕ_{≥ 1}`

Staged statement contract for `PIN-S003.md` v1 (`SeamC.A385590.triangle_bijective_posNat`),
formalizing Werner Schulte's conjecture (`OEIS A385590`, `%C` line 11 under `%N` line 10,
live revision `#7 Jul 07 2025 20:01:36`).
-/

namespace SeamC.A385590

/-- Fibonacci sequence `OEIS A000045` (`F(0) = 0, F(1) = 1, F(n + 2) = F(n) + F(n + 1)`). -/
abbrev F : ℕ → ℕ := Nat.fib

/-- Lower Fibonacci inverse `OEIS A130233`: greatest `i` with `F(i) ≤ n`.
For every `n ≥ 1`, this is the unique `i ≥ 2` satisfying `F(i) ≤ n < F(i + 1)`. -/
def blockIndex (n : ℕ) : ℕ :=
  Nat.greatestFib n

/-- For every `n ≥ 1`, `i = blockIndex n` satisfies `2 ≤ i` and `F(i) ≤ n < F(i + 1)`. -/
theorem blockIndex_spec {n : ℕ} (hn : 1 ≤ n) :
    2 ≤ blockIndex n ∧ F (blockIndex n) ≤ n ∧ n < F (blockIndex n + 1) :=
  ⟨Nat.le_greatestFib.mpr hn, Nat.fib_greatestFib_le n, Nat.lt_fib_greatestFib_add_one n⟩

/-- Unique Fibonacci block index (`L1` existence and uniqueness): for every `n ≥ 1`, there exists
a unique `i : ℕ` with `2 ≤ i ∧ F(i) ≤ n ∧ n < F(i + 1)`, namely `blockIndex n`. -/
theorem fibBlockIndex_existsUnique {n : ℕ} (hn : 1 ≤ n) :
    ∃! i : ℕ, 2 ≤ i ∧ F i ≤ n ∧ n < F (i + 1) := by
  refine ⟨blockIndex n, blockIndex_spec hn, ?_⟩
  rintro i ⟨_, hle, hlt⟩
  exact Nat.le_antisymm (Nat.le_greatestFib.mpr hle)
    (Nat.lt_succ_iff.mp (Nat.greatestFib_lt.mpr hlt))

/-- `OEIS A385590` (`%N` line 10): Fibonacci triangle `T(n, k)` defined for `1 ≤ k ≤ n` by
`T(n, k) = F(i - 1)^2 + 1 - ((i - 1) % 2) + (n - F(i)) * F(i - 2) + (k - 1) * F(i - 1)`
where `i = blockIndex n = A130233(n)`. -/
def T (n k : ℕ) : ℕ :=
  let i := blockIndex n
  F (i - 1) ^ 2 + 1 - ((i - 1) % 2) + (n - F i) * F (i - 2) + (k - 1) * F (i - 1)

/-- Positivity of `T(n, k)` across `1 ≤ n`: since `i ≥ 2` gives `F(i - 1) ≥ 1` and
`((i - 1) % 2) ≤ 1`, `(F(i - 1)^2 + 1) - ((i - 1) % 2) ≥ 1`. -/
theorem one_le_T {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : 1 ≤ T n k := by
  dsimp only [T]
  have hi : 2 ≤ blockIndex n := (blockIndex_spec hn).1
  have hpos : 0 < F (blockIndex n - 1) := Nat.fib_pos.mpr (by omega)
  have hsq : 1 ≤ F (blockIndex n - 1) ^ 2 := by
    simpa using Nat.pow_le_pow_left (Nat.succ_le_of_lt hpos) 2
  have hmod : (blockIndex n - 1) % 2 < 2 := Nat.mod_lt _ Nat.zero_lt_two
  omega

/-- Werner Schulte's conjecture on `OEIS A385590` (`%C` line 11):
the Fibonacci triangle map `T` from `{ p : ℕ × ℕ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1 }`
to `{ m : ℕ // 1 ≤ m }` is `Function.Bijective`. -/
theorem triangle_bijective_posNat :
    Function.Bijective
      (fun q : { p : ℕ × ℕ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1 } =>
        (⟨T q.val.1 q.val.2, one_le_T q.property.1 q.val.2⟩ : { m : ℕ // 1 ≤ m })) := by
  sorry

end SeamC.A385590
