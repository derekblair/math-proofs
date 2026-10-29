import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Function.Iterate -- [Audit §3.2 Item 3 / §3.3 Hazard S1] Explicit import for Nat.iterate (f^[n])

/-!
# OEIS A267442 / A043545 / A036987: Rule 129 and Rule 126 Single-Seed Middle Columns

Pinned target statements for candidate `a267442-eq-a043545` (`derekblair/math-proofs`).
Do NOT modify any `def` or `theorem` signature or definition body in this file once frozen.

## Audited Route A Proof-Lane Notes (Informational — Not Pinned Declarations)

* **[Audit §1.4 Repair A2-1 — Uniform `Bool` closed form]:** Define the Rule 126 space-time
  closed form with uniform `Bool` branches (avoiding `Prop`/`Bool` branch mismatch):
  `def B (n : Nat) (x : Int) : Bool :=`
  `  if x.natAbs ≤ n then Nat.choose n ((n - x.natAbs) / 2) % 2 == 1 else false`
* **[Audit §1.4 Repair A2-2 — Truncated-subtraction-safe indexing]:** Keep `n - x.natAbs`
  strictly inside `if x.natAbs ≤ n` so exterior cells (`x.natAbs > n`) never evaluate truncated
  `0`. After spatial reflection (`B n (-x) = B n x` and `ecaRule 126 r q p = ecaRule 126 p q r`),
  split `0 ≤ x` via `Int.le_total 0 x` and write `x = (m : Int)` for `m : Nat` (with `m = m' + 1`
  on positive interior cells so `(x - 1).natAbs = m'`, `x.natAbs = m' + 1`,
  `(x + 1).natAbs = m' + 2`). In positive even subcases, write `u = 2 * (j' + 1)` (interior
  Case 4a) and `n = 2 * (k' + 1)` (origin Case 5a) so `Nat.choose_succ_succ'` applies directly
  with zero `j - 1` or `k - 1` subtraction obligations.
* **[Audit §1.4 Repair A2-3 — Outer-step iterate unfolding]:** `(ecaStep R)^[n + 1] singleSeed`
  reduces definitionally (`Function.iterate_succ_apply`) to `(ecaStep R)^[n] (ecaStep R singleSeed)`,
  not `ecaStep R ((ecaStep R)^[n] singleSeed)`. Start inductive steps on `n` by rewriting with
  `Function.iterate_succ_apply'` (`rw [ecaOrbit, Function.iterate_succ_apply', ← ecaOrbit]`).
* **[Audit §1.5 Repair A3-1 — Exact Mathlib Lucas theorem identifier]:** In Mathlib `v4.34.1`
  (`Mathlib.Data.Nat.Choose.Lucas` + `Mathlib.Data.Nat.Prime.Defs`), one-step Lucas mod `p` lives
  in namespace `Choose` (not `Nat`): supply `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩` and
  apply `Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * k + 1) (k := k) (p := 2)`.
* **[Audit §1.5 Repair A3-2 — `Bool`-to-`Nat` bridges]:** Relate `B n 0 : Bool` to
  `g n := n.choose (n / 2) % 2 : Nat` via `B n 0 = true ↔ g n = 1` (`Nat.mod_two_eq_zero_or_one`)
  to prove `rule126_middle_column_iff` first; deduce `rule126_middle_column_eq_a036987` via
  `by_cases h : ∃ m : Nat, n = 2 ^ m - 1` (`if_pos` / `if_neg` on `Bool.toNat`); and deduce
  `a267442_eq_a043545` for `0 < n` using `∀ b : Bool, (!b).toNat = 1 - b.toNat`.
* **[Audit §3.3 Hazard S5 — Kernel-only finite `Bool` proofs]:** Discharge 3-bit `Bool` truth-table
  identities (`Lemma A1`, `C0`, `C1`) strictly via explicit case splits
  (`cases p <;> cases q <;> cases r <;> rfl`) or kernel `Decidable.decide`. Never invoke
  compiler-backed reduction or SAT/bitvector reflection tactics, which emit forbidden trust axioms
  outside `[propext, Classical.choice, Quot.sound]`.
-/

namespace Mathproofs.Rule129MiddleColumn

-- [Audit §3.3 Hazard S4] Verified exact Wolfram bit encoding b_{4p + 2q + r}(R) via Nat.testBit.
/-- Wolfram elementary cellular automaton local rule `R` (`0 ≤ R < 256`) on `Bool`:
neighborhood `(p, q, r)` reads bit `4 * p + 2 * q + r` of `R`. -/
def ecaRule (R : Nat) (p q r : Bool) : Bool :=
  R.testBit (4 * p.toNat + 2 * q.toNat + r.toNat)

-- [Audit §3.2 Item 5 & §3.3 Hazard S4] Total configuration Int → Bool preserves Rule 129 background
-- (0 at n = 0, transitioning 0 -> 1 at n = 1 and remaining 1 for all n ≥ 1 outside the light cone).
/-- One global synchronous step of rule `R` on the infinite integer lattice `Int → Bool`. -/
def ecaStep (R : Nat) (c : Int → Bool) : Int → Bool :=
  fun x => ecaRule R (c (x - 1)) (c x) (c (x + 1))

/-- Single ON (black) cell at `x = 0` in an infinite OFF (white) background. -/
def singleSeed : Int → Bool :=
  fun x => x == 0

-- [Audit §3.3 Hazard S1 & §1.4 Repair A2-3] Unchanged definition backed by explicit
-- `import Mathlib.Logic.Function.Iterate`; unfold generation `n + 1` via `Function.iterate_succ_apply'`.
/-- Configuration at generation `n` starting from `singleSeed` under rule `R`. -/
def ecaOrbit (R : Nat) (n : Nat) : Int → Bool :=
  (ecaStep R)^[n] singleSeed

/-- OEIS A267442: middle column (`x = 0`) of ECA Rule 129 from `singleSeed` (`0`/`1`-valued). -/
def a267442 (n : Nat) : Nat :=
  (ecaOrbit 129 n 0).toNat

-- [Audit §3.3 Hazard S2] Retains primary `∃ m : Nat, n = 2 ^ m - 1` characterization (%F A036987);
-- legitimately uses `Classical.choice` (allowed by pin manifest) — do not substitute bitwise expressions.
/-- OEIS A036987 (Fredholm-Rueppel sequence): `1` iff `n = 2 ^ m - 1` for some `m : Nat`, else `0`. -/
noncomputable def a036987 (n : Nat) : Nat :=
  open Classical in
  if ∃ m : Nat, n = 2 ^ m - 1 then 1 else 0

-- [Audit §3.2 Item 5 & §3.3 Hazard S3] Primary Kimberling %N A043545 digit-spread definition;
-- in Mathlib `Nat.digits 2 0 = []`, which the explicit `| [] => 0` branch maps to `0` (`0 = (0)_2`).
/-- OEIS A043545: `(maximal base-2 digit of n) - (minimal base-2 digit of n)`, offset `0`. -/
def a043545 (n : Nat) : Nat :=
  match Nat.digits 2 n with
  | [] => 0
  | d :: ds => ds.foldl max d - ds.foldl min d

/-- Rule 126 middle-column theorem (iff form): `C_126(n, 0) = true ↔ ∃ m, n = 2 ^ m - 1`. -/
theorem rule126_middle_column_iff (n : Nat) :
    ecaOrbit 126 n 0 = true ↔ ∃ m : Nat, n = 2 ^ m - 1 := by
  sorry

/-- Rule 126 middle-column theorem (sequence form): `(C_126(n, 0)).toNat = A036987(n)` for all `n`. -/
theorem rule126_middle_column_eq_a036987 (n : Nat) :
    (ecaOrbit 126 n 0).toNat = a036987 n := by
  sorry

/-- R. J. Mathar's conjecture (OEIS A267442, Jan 17 2016): `A267442(n) = A043545(n)` for all `n > 0`. -/
theorem a267442_eq_a043545 (n : Nat) (hn : 0 < n) :
    a267442 n = a043545 n := by
  sorry

end Mathproofs.Rule129MiddleColumn
