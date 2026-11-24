import Mathlib.Data.Nat.Nth

/-!
# Seam B Entry C018 (OEIS A189640 1-Positions = A026232): Frozen Statement

Verbatim transcription of the definitions and theorem signatures from the frozen
pin manifest `PIN-C018.md` v1
(`sha256: da0d52a6d4966c8908f92a046556ccf952b73d25139d9c66b5a81e5d18ba3a69`),
placed under `namespace MathProofs.SeamB.C018` per the `math-proofs` repository
convention.
-/

namespace MathProofs.SeamB.C018

/-- Morphism `0 -> 001, 1 -> 101` on `{0, 1}` (`Fin 2`). -/
def a189640Morph : Fin 2 → List (Fin 2)
  | 0 => [0, 0, 1]
  | 1 => [1, 0, 1]

/-- `m`-th morphism iterate starting from seed `[0]` (length `3^m`). -/
def a189640Iter : ℕ → List (Fin 2)
  | 0 => [0]
  | m + 1 => (a189640Iter m).flatMap a189640Morph

/-- 1-based fixed-point sequence `A189640(n)` for `n ≥ 1` (`0` at `n = 0`). -/
def a189640 (n : ℕ) : ℕ :=
  if n = 0 then 0 else (((a189640Iter n)[n - 1]?).map Fin.val).getD 0

/-- 1-based `0`-position enumeration of `A189640` (companion C017). -/
noncomputable def a189640ZeroPos (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun k => 1 ≤ k ∧ a189640 k = 0) (n - 1)

/-- 1-based `1`-position enumeration of `A189640` (LHS of C018). -/
noncomputable def a189640OnePos (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun k => 1 ≤ k ∧ a189640 k = 1) (n - 1)

/-- Step-by-step partial array state of Kimberling's left-right filling algorithm
initialized at `a(1) = 1`. -/
def lrState (h : ℕ → ℕ) : ℕ → ℕ → Option ℕ
  | 0 => fun _ => none
  | 1 => fun k => if k = 1 then some 1 else none
  | m + 2 =>
    let st := lrState h (m + 1)
    let n := m + 2
    let d := h n
    let L := n - d
    let R := n + d
    let target := if (st L).isNone then L else R
    fun k => if k = target then some n else st k

/-- Total sequence reading the value assigned at index `k` at the earliest step
`m` where `k` becomes defined. -/
noncomputable def lrFill (h : ℕ → ℕ) (k : ℕ) : ℕ :=
  let m := sInf {m : ℕ | (lrState h m k).isSome}
  (lrState h m k).getD 0

/-- OEIS `A026166(k)` for `k ≥ 1` via `lrFill` with `h(n) = (n - 1) / 2`. -/
noncomputable def a026166 (k : ℕ) : ℕ :=
  lrFill (fun n => (n - 1) / 2) k

/-- OEIS `A026142(k)` for `k ≥ 1` via `lrFill` with `h(n) = (n + 1) / 2`. -/
noncomputable def a026142 (k : ℕ) : ℕ :=
  lrFill (fun n => (n + 1) / 2) k

/-- OEIS `A026231(n)`: 1-based `n`-th positive index `k ≥ 1` satisfying
`A026166(k) = A026142(k) + 1`. -/
noncomputable def a026231 (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun k => 1 ≤ k ∧ a026166 k = a026142 k + 1) (n - 1)

/-- OEIS `A026232(n) = (A026231(n) + 1) / 3` for `n ≥ 1` (RHS of C018). -/
noncomputable def a026232 (n : ℕ) : ℕ :=
  if n = 0 then 0 else (a026231 n + 1) / 3

/-- Integrality theorem: for all `n ≥ 1`, `A026231(n) % 3 = 2`, ensuring exact
division by `3` in `A026232(n) = (A026231(n) + 1) / 3`. -/
theorem a026231_mod_three (n : ℕ) (hn : 1 ≤ n) :
    a026231 n % 3 = 2 := by
  sorry

/-- Primary C018 positional identity: for all `n ≥ 1`, the `n`-th 1-based
`1`-position of `A189640` equals `A026232(n)`. -/
theorem a189640_onePos_eq_a026232 (n : ℕ) (hn : 1 ≤ n) :
    a189640OnePos n = a026232 n := by
  sorry

end MathProofs.SeamB.C018
