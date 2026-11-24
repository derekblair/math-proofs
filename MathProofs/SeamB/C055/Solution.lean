import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Seam B Entry C055 (OEIS A266664): Colin Barker Rule 47 OFF-Cell Conjecture Bundle

Formalizes and proves Colin Barker's three-part conjecture bundle on `OEIS A266664`
(`%F` lines 17–21, Jan 03 2016 and Apr 18 2019; authored by Robert Price, Jan 02 2016)
together with the explicit Rule 47 truth table (`rule47_truth_table`), explicit initial
values (`a 0 = 0`, `a 1 = 1`), and the bundled conjunction `c055_bundle`, against the
frozen target contract `PIN-C055.md` v1
(`sha256: 9a261730585d5000f09182e4980025ca1ae486554d384e340214e840a768f69e`,
`Statement.lean sha256: 9a8740906a620cf9b89f613583d7bd3a8aaab162a66e200d013c15cc6ba53e8d`,
`delta_vs_source: NONE`), completely standalone via the 1-step shifting 2-cell defect
invariant route in `SCOPING-C055.md` (§2, §5, §7):

1. **Wolfram Rule 47 truth table and algebraic reduction (`rule47_truth_table`, `rule47_eq`,
   `rule47_not_eq`, `rule47_not_symm`)**: verifies all 8 Boolean triples of
   `(47 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)` by pure kernel reduction (`rfl`)
   and establishes both the ON normal form `(!l) || (!c && r)` and OFF normal form
   `l && (c || !r)`.
2. **Initial values and transient generations `n = 0, 1, 2` (`ca_zero`, `a_zero`, `ca_one`,
   `a_one`, `ca_two`)**: proves `a 0 = 0`, establishes `ca 1 j = decide (j ≠ 1)` and
   `a 1 = 1`, and proves that at `n = 2` bit `5` (`101 ↦ 1`) widens the single-cell defect
   `{1}` into the persistent 2-cell ON defect `ca 2 j = decide (j = 1 ∨ j = 2)` on all of `ℤ`.
3. **1-step shifting 2-cell defect + alternating-exterior invariant on `ℤ` (`ca_step_xor`,
   `ca_profile`, `ca_even_pos`, `ca_odd_pos`)**: proves by 1-step induction from `n = 2` that
   `ca n j = xor (decide (Odd n)) (decide (j = (n : ℤ) - 1 ∨ j = (n : ℤ)))` for all `n ≥ 2`
   and all `j : ℤ`, evolving globally on `ℤ` before restricting to `[-n, n]` inside `a n`.
4. **OFF-cell window counts, rational closed form, and 4-step recurrence (`a_even_pos`,
   `a_odd_pos`, `a_closed_form`, `a_recurrence`)**: deduces `a (2*m) = 4*m - 1` and
   `a (2*m + 1) = 2` for all `m ≥ 1`, Barker's exact rational closed form for `1 < n`, and
   the 4-step linear recurrence `(a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)` for `5 < n`.
5. **Rational ordinary generating function and bundle (`a_gf`, `c055_bundle`,
   `a_gf_denom_isUnit`, `a_gf_unit_inv`)**: rewrites
   `((1 - X)^2 * (1 + X)^2) * F = F - 2 * (X^2 * F) + X^4 * F` and
   `X * (1 + 3*X + X^3 - X^4) = X + 3*X^2 + X^4 - X^5` in `PowerSeries ℚ`, proves equality
   coefficientwise via `PowerSeries.ext` and `PowerSeries.coeff_X_pow_mul'`, and establishes
   unit invertibility of `(1 - X)^2 * (1 + X)^2` and the lossless inverse-series quotient.
6. **Structural and non-vacuity extensions (`aOn`, `a_add_aOn`, `ca_all_triples_occur`,
   `ca_no_010_ge2`, `ca_no_101_ge2`, `caRule_eq_ca_iff`, `rule117_eq_rule47_rev`,
   `ca117_eq_ca_neg`, `a117_eq_a`, `a_dp_eq_a`, `a_dp_spot_0_to_12`, `a_spot_0_to_12`,
   `a_closed_form_false_zero`, `a_closed_form_false_one`, `a_recurrence_false_four`,
   `a_recurrence_false_five`, `aConeClamp_two_eq_two`, `aBoxClamp_two_eq_two`)**.
-/

namespace Mathproofs.A266664

/-- Wolfram Rule 47 elementary cellular automaton local rule (`47 = 0b00101111`):
maps `(l, c, r)` to bit `4 * l.toNat + 2 * c.toNat + r.toNat` of `47`. -/
def rule47 (l c r : Bool) : Bool := (47 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Bi-infinite 1D evolution of Rule 47 on `ℤ` starting from a single ON (`true`) cell at `0`. -/
def ca : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule47 (ca n (j - 1)) (ca n j) (ca n (j + 1))

/-- OEIS A266664: number of OFF (`false` / white) cells in the active light-cone window
`[-n, n]` at generation `n`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca n j))).card

/-! ### Step 1: Rule 47 truth table and algebraic Boolean normal forms -/

/-- Explicit 8-entry truth-table verification of `rule47` (`0b00101111`). -/
theorem rule47_truth_table :
    rule47 false false false = true ∧ rule47 false false true = true ∧
    rule47 false true false = true ∧ rule47 false true true = true ∧
    rule47 true false false = false ∧ rule47 true false true = true ∧
    rule47 true true false = false ∧ rule47 true true true = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Minimal ON Boolean normal form of Rule 47: `rule47 l c r = (!l) || (!c && r)`. -/
theorem rule47_eq (l c r : Bool) : rule47 l c r = ((!l) || (!c && r)) := by
  cases l <;> cases c <;> cases r <;> rfl

/-- Minimal OFF Boolean normal form of Rule 47: `!(rule47 l c r) = l && (c || !r)`. -/
theorem rule47_not_eq (l c r : Bool) : !(rule47 l c r) = (l && (c || !r)) := by
  cases l <;> cases c <;> cases r <;> rfl

/-- Rule 47 breaks left-right reflection symmetry (`rule47 0 0 1 = true ≠ false = rule47 1 0 0`). -/
theorem rule47_not_symm : rule47 false false true ≠ rule47 true false false := by
  intro h
  cases h

/-! ### Step 2: Initial values `a 0 = 0`, `a 1 = 1`, and transient generations `n = 0, 1, 2` on `ℤ` -/

theorem ca_zero (j : ℤ) : ca 0 j = decide (j = 0) :=
  rfl

/-- Pinned seed OFF-cell count at generation `n = 0`: `a 0 = 0`. -/
theorem a_zero : a 0 = 0 := by
  unfold a
  have hfilter :
      (Finset.Icc (-(0 : ℕ) : ℤ) (0 : ℕ)).filter (fun j => !(ca 0 j)) = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, Nat.cast_zero,
      neg_zero, not_and]
    intro ⟨hlo, hhi⟩ hneg
    have hj : j = 0 := by omega
    subst hj
    exact Bool.false_ne_true hneg
  rw [hfilter, Finset.card_empty]

/-- Generation `n = 1` on all of `ℤ`: only `j = 1` is OFF (`false`), while every other
cell on `ℤ` (including the infinite exterior `|j| > 1`) is ON (`true`). -/
theorem ca_one (j : ℤ) : ca 1 j = decide (j ≠ 1) := by
  change rule47 (decide (j - 1 = 0)) (decide (j = 0)) (decide (j + 1 = 0)) = decide (j ≠ 1)
  rw [rule47_eq]
  by_cases h1 : j = 1
  · subst h1
    rfl
  · have hl : ¬(j - 1 = 0) := by omega
    rw [decide_eq_false hl, decide_eq_true h1]
    rfl

/-- Pinned OFF-cell count at generation `n = 1`: `a 1 = 1`. -/
theorem a_one : a 1 = 1 := by
  unfold a
  have hfilter :
      (Finset.Icc (-(1 : ℕ) : ℤ) (1 : ℕ)).filter (fun j => !(ca 1 j)) = {(1 : ℤ)} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, ca_one,
      Bool.not_eq_true', decide_eq_false_iff_not]
    omega
  rw [hfilter, Finset.card_singleton]

/-- Generation `n = 2` on all of `ℤ`: the isolated-OFF triple `(1, 0, 1)` at `j = 1` activates
bit `5` of `47`, widening `{1}` into the persistent 2-cell ON defect `{1, 2}` in an all-OFF
exterior. -/
theorem ca_two (j : ℤ) : ca 2 j = decide (j = 1 ∨ j = 2) := by
  change rule47 (ca 1 (j - 1)) (ca 1 j) (ca 1 (j + 1)) = decide (j = 1 ∨ j = 2)
  rw [rule47_eq, ca_one (j - 1), ca_one j, ca_one (j + 1)]
  by_cases h1 : j = 1
  · subst h1
    rfl
  · by_cases h2 : j = 2
    · subst h2
      rfl
    · have hl : j - 1 ≠ 1 := by omega
      have hrhs : ¬(j = 1 ∨ j = 2) := by omega
      rw [decide_eq_true hl, decide_eq_true h1, decide_eq_false hrhs]
      rfl

/-! ### Step 3: 1-step shifting 2-cell defect + alternating-exterior invariant on `ℤ` (`n ≥ 2`) -/

/-- Single-step polarity-flipping right-edge glider step on `ℤ`: for any uniform background `b`,
a 2-cell defect `{n - 1, n}` inverted against `b` advances rightward by `+1` to `{n, n + 1}`
inverted against `!b`. -/
theorem ca_step_xor (n : ℕ) (b : Bool)
    (h : ∀ j : ℤ, ca n j = xor b (decide (j = (n : ℤ) - 1 ∨ j = (n : ℤ)))) :
    ∀ j : ℤ, ca (n + 1) j = xor (!b) (decide (j = (n : ℤ) ∨ j = (n : ℤ) + 1)) := by
  intro j
  change rule47 (ca n (j - 1)) (ca n j) (ca n (j + 1)) =
    xor (!b) (decide (j = (n : ℤ) ∨ j = (n : ℤ) + 1))
  rw [rule47_eq, h (j - 1), h j, h (j + 1)]
  cases b
  · by_cases hjn : j = (n : ℤ)
    · subst hjn
      rw [decide_eq_true (by omega : (n : ℤ) - 1 = (n : ℤ) - 1 ∨ (n : ℤ) - 1 = (n : ℤ)),
          decide_eq_true (by omega : (n : ℤ) = (n : ℤ) - 1 ∨ (n : ℤ) = (n : ℤ)),
          decide_eq_true (Or.inl rfl)]
      rfl
    · by_cases hjn1 : j = (n : ℤ) + 1
      · subst hjn1
        rw [decide_eq_true (by omega : (n : ℤ) + 1 - 1 = (n : ℤ) - 1 ∨ (n : ℤ) + 1 - 1 = (n : ℤ)),
            decide_eq_false (by omega : ¬((n : ℤ) + 1 = (n : ℤ) - 1 ∨ (n : ℤ) + 1 = (n : ℤ))),
            decide_eq_false (by omega : ¬((n : ℤ) + 1 + 1 = (n : ℤ) - 1 ∨ (n : ℤ) + 1 + 1 = (n : ℤ))),
            decide_eq_true (Or.inr rfl)]
        rfl
      · have hl : ¬(j - 1 = (n : ℤ) - 1 ∨ j - 1 = (n : ℤ)) := by omega
        have hrhs : ¬(j = (n : ℤ) ∨ j = (n : ℤ) + 1) := by omega
        rw [decide_eq_false hl, decide_eq_false hrhs]
        rfl
  · by_cases hjn : j = (n : ℤ)
    · subst hjn
      rw [decide_eq_true (by omega : (n : ℤ) - 1 = (n : ℤ) - 1 ∨ (n : ℤ) - 1 = (n : ℤ)),
          decide_eq_true (Or.inl rfl)]
      rfl
    · by_cases hjn1 : j = (n : ℤ) + 1
      · subst hjn1
        rw [decide_eq_true (by omega : (n : ℤ) + 1 - 1 = (n : ℤ) - 1 ∨ (n : ℤ) + 1 - 1 = (n : ℤ)),
            decide_eq_true (Or.inr rfl)]
        rfl
      · by_cases hjm : j = (n : ℤ) - 1
        · subst hjm
          rw [decide_eq_false (by omega : ¬((n : ℤ) - 1 - 1 = (n : ℤ) - 1 ∨ (n : ℤ) - 1 - 1 = (n : ℤ))),
              decide_eq_true (by omega : (n : ℤ) - 1 = (n : ℤ) - 1 ∨ (n : ℤ) - 1 = (n : ℤ)),
              decide_eq_true (by omega : (n : ℤ) - 1 + 1 = (n : ℤ) - 1 ∨ (n : ℤ) - 1 + 1 = (n : ℤ)),
              decide_eq_false (by omega : ¬((n : ℤ) - 1 = (n : ℤ) ∨ (n : ℤ) - 1 = (n : ℤ) + 1))]
          rfl
        · have hl : ¬(j - 1 = (n : ℤ) - 1 ∨ j - 1 = (n : ℤ)) := by omega
          have hc : ¬(j = (n : ℤ) - 1 ∨ j = (n : ℤ)) := by omega
          have hrhs : ¬(j = (n : ℤ) ∨ j = (n : ℤ) + 1) := by omega
          rw [decide_eq_false hl, decide_eq_false hc, decide_eq_false hrhs]
          rfl

/-- Unified 1-step global `ℤ`-invariant for every `n ≥ 2` and `j ∈ ℤ`:
`ca n j` is the XOR of the exterior background parity (`Odd n`) with the right-moving 2-cell
defect indicator `j ∈ {n - 1, n}`. -/
theorem ca_profile (n : ℕ) (hn : 2 ≤ n) :
    ∀ j : ℤ, ca n j = xor (decide (Odd n)) (decide (j = (n : ℤ) - 1 ∨ j = (n : ℤ))) := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro j
    have hnot : ¬ Odd (2 : ℕ) := by
      rintro ⟨t, ht⟩
      omega
    have hprop : (j = 1 ∨ j = 2) ↔ (j = ((2 : ℕ) : ℤ) - 1 ∨ j = ((2 : ℕ) : ℤ)) := by
      push_cast
      omega
    rw [ca_two j, decide_eq_false hnot, Bool.false_xor, decide_eq_decide.mpr hprop]
  | succ k hk ih =>
    intro j
    have hstep := ca_step_xor k (decide (Odd k)) ih j
    have hodd : (!decide (Odd k)) = decide (Odd (k + 1)) := by
      rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have h1 : ¬ Odd (m + m) := by
          rintro ⟨t, ht⟩
          omega
        have h2 : Odd (m + m + 1) := ⟨m, by omega⟩
        rw [decide_eq_false h1, decide_eq_true h2]
        rfl
      · have h1 : Odd (2 * m + 1) := ⟨m, rfl⟩
        have h2 : ¬ Odd (2 * m + 1 + 1) := by
          rintro ⟨t, ht⟩
          omega
        rw [decide_eq_true h1, decide_eq_false h2]
        rfl
    have hprop :
        (j = (k : ℤ) ∨ j = (k : ℤ) + 1) ↔
        (j = ((k + 1 : ℕ) : ℤ) - 1 ∨ j = ((k + 1 : ℕ) : ℤ)) := by
      push_cast
      omega
    rw [hstep, hodd, decide_eq_decide.mpr hprop]

/-- Global `ℤ`-invariant at positive even generations `2m` (`m ≥ 1`): ON solely on
`{2m - 1, 2m}`, OFF everywhere else. -/
theorem ca_even_pos (m : ℕ) (hm : 1 ≤ m) (j : ℤ) :
    ca (2 * m) j = decide (j = 2 * (m : ℤ) - 1 ∨ j = 2 * (m : ℤ)) := by
  have hnot : ¬ Odd (2 * m) := by
    rintro ⟨t, ht⟩
    omega
  have hprop :
      (j = ((2 * m : ℕ) : ℤ) - 1 ∨ j = ((2 * m : ℕ) : ℤ)) ↔
      (j = 2 * (m : ℤ) - 1 ∨ j = 2 * (m : ℤ)) := by
    push_cast
    omega
  rw [ca_profile (2 * m) (by omega) j, decide_eq_false hnot, Bool.false_xor,
      decide_eq_decide.mpr hprop]

/-- Global `ℤ`-invariant at odd generations `2m + 1` (`m ≥ 1`): OFF solely on
`{2m, 2m + 1}`, ON everywhere else. -/
theorem ca_odd_pos (m : ℕ) (hm : 1 ≤ m) (j : ℤ) :
    ca (2 * m + 1) j = !decide (j = 2 * (m : ℤ) ∨ j = 2 * (m : ℤ) + 1) := by
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have hprop :
      (j = ((2 * m + 1 : ℕ) : ℤ) - 1 ∨ j = ((2 * m + 1 : ℕ) : ℤ)) ↔
      (j = 2 * (m : ℤ) ∨ j = 2 * (m : ℤ) + 1) := by
    push_cast
    omega
  rw [ca_profile (2 * m + 1) (by omega) j, decide_eq_true hodd, Bool.true_xor,
      decide_eq_decide.mpr hprop]

/-! ### Step 4: OFF-cell window counting on `[-n, n]` and Barker's rational closed form (`1 < n`) -/

/-- Exact OFF-cell count at positive even generations: `a (2m) = 4m - 1` for all `m ≥ 1`. -/
theorem a_even_pos (m : ℕ) (hm : 1 ≤ m) : a (2 * m) = 4 * m - 1 := by
  unfold a
  have hfilter :
      (Finset.Icc (-((2 * m : ℕ) : ℤ)) ((2 * m : ℕ) : ℤ)).filter
          (fun j => !(ca (2 * m) j)) =
        Finset.Icc (-((2 * m : ℕ) : ℤ)) (2 * (m : ℤ) - 2) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, ca_even_pos m hm, Bool.not_eq_true',
      decide_eq_false_iff_not]
    push_cast
    omega
  rw [hfilter, Int.card_Icc]
  push_cast
  omega

/-- Exact OFF-cell count at odd generations `2m + 1` (`m ≥ 1`): `a (2m + 1) = 2`. -/
theorem a_odd_pos (m : ℕ) (hm : 1 ≤ m) : a (2 * m + 1) = 2 := by
  unfold a
  have hfilter :
      (Finset.Icc (-((2 * m + 1 : ℕ) : ℤ)) ((2 * m + 1 : ℕ) : ℤ)).filter
          (fun j => !(ca (2 * m + 1) j)) =
        ({2 * (m : ℤ), 2 * (m : ℤ) + 1} : Finset ℤ) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      ca_odd_pos m hm, Bool.not_not, decide_eq_true_eq]
    push_cast
    omega
  rw [hfilter, Finset.card_pair (by omega : 2 * (m : ℤ) ≠ 2 * (m : ℤ) + 1)]

theorem a_two : a 2 = 3 := by
  simpa using a_even_pos 1 (by omega)

theorem a_three : a 3 = 2 := by
  simpa using a_odd_pos 1 (by omega)

theorem a_four : a 4 = 7 := by
  simpa using a_even_pos 2 (by omega)

theorem a_five : a 5 = 2 := by
  simpa using a_odd_pos 2 (by omega)

/-- Colin Barker's closed form for `A266664(n)` for `n > 1`. -/
theorem a_closed_form (n : ℕ) (hn : 1 < n) :
    (a n : ℚ) = (2 * (-1 : ℚ) ^ n * (n : ℚ) + 2 * (n : ℚ) - 3 * (-1 : ℚ) ^ n + 1) / 2 := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hm : 1 ≤ m := by omega
    rw [show m + m = 2 * m by omega, a_even_pos m hm]
    have hpow : (-1 : ℚ) ^ (2 * m) = 1 := by
      rw [pow_mul]
      norm_num
    rw [hpow, Nat.cast_sub (by omega : 1 ≤ 4 * m)]
    push_cast
    ring
  · have hm : 1 ≤ m := by omega
    rw [a_odd_pos m hm]
    have hpow : (-1 : ℚ) ^ (2 * m + 1) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    rw [hpow]
    push_cast
    ring

/-! ### Step 5: Four-step linear recurrence (`5 < n`) -/

/-- Colin Barker's 4-step linear recurrence for `A266664(n)` for `n > 5`. -/
theorem a_recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hm : 3 ≤ m := by omega
    have h0 : m + m = 2 * m := by omega
    have h2 : 2 * m - 2 = 2 * (m - 1) := by omega
    have h4 : 2 * m - 4 = 2 * (m - 2) := by omega
    rw [h0, h2, h4, a_even_pos m (by omega), a_even_pos (m - 1) (by omega),
        a_even_pos (m - 2) (by omega)]
    omega
  · have hm : 3 ≤ m := by omega
    have h2 : 2 * m + 1 - 2 = 2 * (m - 1) + 1 := by omega
    have h4 : 2 * m + 1 - 4 = 2 * (m - 2) + 1 := by omega
    rw [h2, h4, a_odd_pos m (by omega), a_odd_pos (m - 1) (by omega),
        a_odd_pos (m - 2) (by omega)]
    norm_num

/-! ### Step 6: Rational ordinary generating function in `PowerSeries ℚ` and C055 bundle -/

/-- Colin Barker's ordinary generating function for `A266664` in `PowerSeries ℚ`. -/
theorem a_gf :
    ((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 * (1 + PowerSeries.X : PowerSeries ℚ) ^ 2) *
      PowerSeries.mk (fun n => (a n : ℚ)) =
    (PowerSeries.X : PowerSeries ℚ) *
      (1 + 3 * PowerSeries.X + PowerSeries.X ^ 3 - PowerSeries.X ^ 4) := by
  let X : PowerSeries ℚ := PowerSeries.X
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hlhs : ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) * F =
      F - 2 * (X ^ 2 * F) + X ^ 4 * F := by ring
  have hrhs : X * (1 + 3 * X + X ^ 3 - X ^ 4) =
      X + 3 * X ^ 2 + X ^ 4 - X ^ 5 := by ring
  change ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) * F =
      X * (1 + 3 * X + X ^ 3 - X ^ 4)
  rw [hlhs, hrhs]
  apply PowerSeries.ext
  intro n
  dsimp only [X, F]
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  rcases n with _ | _ | _ | _ | _ | _ | k
  · norm_num [a_zero]
  · norm_num [a_one]
  · norm_num [a_zero, a_two]
  · norm_num [a_one, a_three]
  · norm_num [a_zero, a_two, a_four]
  · norm_num [a_one, a_three, a_five]
  · have hrec : (a (k + 6) : ℤ) = 2 * (a (k + 4) : ℤ) - (a (k + 2) : ℤ) := by
      simpa using a_recurrence (k + 6) (by omega)
    have hrec_q : (a (k + 6) : ℚ) = 2 * (a (k + 4) : ℚ) - (a (k + 2) : ℚ) := by
      exact_mod_cast hrec
    have h2 : 2 ≤ k + 6 := by omega
    have h4 : 4 ≤ k + 6 := by omega
    have hne1 : k + 6 ≠ 1 := by omega
    have hne2 : k + 6 ≠ 2 := by omega
    have hne4 : k + 6 ≠ 4 := by omega
    have hne5 : k + 6 ≠ 5 := by omega
    simp only [h2, h4, hne1, hne2, hne4, hne5, ↓reduceIte,
      show k + 6 - 2 = k + 4 by omega, show k + 6 - 4 = k + 2 by omega]
    linarith

/-- Full C055 target bundle combining initial values, closed form, recurrence, and g.f. -/
theorem c055_bundle :
    a 0 = 0 ∧
    a 1 = 1 ∧
    (∀ n : ℕ, 1 < n →
      (a n : ℚ) = (2 * (-1 : ℚ) ^ n * (n : ℚ) + 2 * (n : ℚ) - 3 * (-1 : ℚ) ^ n + 1) / 2) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
    (((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 * (1 + PowerSeries.X : PowerSeries ℚ) ^ 2) *
      PowerSeries.mk (fun n => (a n : ℚ)) =
      (PowerSeries.X : PowerSeries ℚ) *
        (1 + 3 * PowerSeries.X + PowerSeries.X ^ 3 - PowerSeries.X ^ 4)) :=
  ⟨a_zero, a_one, a_closed_form, a_recurrence, a_gf⟩

/-! ### Step 7: Unit invertibility, ON-cell complement, Rule 47 uniqueness, and Mirror Rule 117 -/

/-- The cleared denominator `(1 - X)^2 * (1 + X)^2` has constant coefficient `1 ≠ 0` and
is therefore a unit in `PowerSeries ℚ`. -/
theorem a_gf_denom_isUnit :
    IsUnit ((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 *
      (1 + PowerSeries.X : PowerSeries ℚ) ^ 2) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_mul, map_pow, map_sub, map_add, map_one, PowerSeries.constantCoeff_X]
  norm_num

/-- Lossless inverse-series quotient form of `a_gf` in `PowerSeries ℚ`. -/
theorem a_gf_unit_inv :
    PowerSeries.mk (fun n => (a n : ℚ)) =
      ((PowerSeries.X : PowerSeries ℚ) *
        (1 + 3 * PowerSeries.X + PowerSeries.X ^ 3 - PowerSeries.X ^ 4)) *
      ((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 *
        (1 + PowerSeries.X : PowerSeries ℚ) ^ 2)⁻¹ := by
  have hcc : PowerSeries.constantCoeff
      ((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 *
        (1 + PowerSeries.X : PowerSeries ℚ) ^ 2) ≠ 0 := by
    simp only [map_mul, map_pow, map_sub, map_add, map_one, PowerSeries.constantCoeff_X]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel
    ((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 *
      (1 + PowerSeries.X : PowerSeries ℚ) ^ 2) hcc
  calc
    PowerSeries.mk (fun n => (a n : ℚ))
        = PowerSeries.mk (fun n => (a n : ℚ)) *
            (((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 *
                (1 + PowerSeries.X : PowerSeries ℚ) ^ 2) *
              ((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 *
                (1 + PowerSeries.X : PowerSeries ℚ) ^ 2)⁻¹) := by
          rw [hinv, mul_one]
    _ = (((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 *
            (1 + PowerSeries.X : PowerSeries ℚ) ^ 2) *
          PowerSeries.mk (fun n => (a n : ℚ))) *
          ((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 *
            (1 + PowerSeries.X : PowerSeries ℚ) ^ 2)⁻¹ := by
          ring
    _ = ((PowerSeries.X : PowerSeries ℚ) *
          (1 + 3 * PowerSeries.X + PowerSeries.X ^ 3 - PowerSeries.X ^ 4)) *
        ((1 - PowerSeries.X : PowerSeries ℚ) ^ 2 *
          (1 + PowerSeries.X : PowerSeries ℚ) ^ 2)⁻¹ := by
          rw [a_gf]

/-- Companion ON-cell count on `[-n, n]` (`OEIS A266662`). -/
def aOn (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j)).card

/-- Exact OFF/ON complement law on the active window `[-n, n]`: `a n + aOn n = 2n + 1`. -/
theorem a_add_aOn (n : ℕ) : a n + aOn n = 2 * n + 1 := by
  unfold a aOn
  have hdisj :
      Disjoint
        ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca n j)))
        ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j)) := by
    rw [Finset.disjoint_filter]
    intro j _ h1 h2
    rw [h2] at h1
    exact Bool.false_ne_true h1
  have hunion :
      ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca n j))) ∪
        ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j)) =
      Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter]
    cases ca n j <;> simp
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Int.card_Icc]
  omega

/-- All 8 local 3-bit neighborhoods occur during generations `n = 0` and `n = 1` of Rule 47
(`000`, `001`, `010`, `100` at `n = 0`; `011`, `101`, `110`, `111` at `n = 1`). -/
theorem ca_all_triples_occur (l c r : Bool) :
    ∃ n : ℕ, ∃ j : ℤ, n ≤ 1 ∧
      ca n (j - 1) = l ∧ ca n j = c ∧ ca n (j + 1) = r := by
  cases l <;> cases c <;> cases r
  · exact ⟨0, 2, by omega, rfl, rfl, rfl⟩
  · exact ⟨0, -1, by omega, rfl, rfl, rfl⟩
  · exact ⟨0, 0, by omega, rfl, rfl, rfl⟩
  · exact ⟨1, 2, by omega, by rw [ca_one]; rfl, by rw [ca_one]; rfl, by rw [ca_one]; rfl⟩
  · exact ⟨0, 1, by omega, rfl, rfl, rfl⟩
  · exact ⟨1, 1, by omega, by rw [ca_one]; rfl, by rw [ca_one]; rfl, by rw [ca_one]; rfl⟩
  · exact ⟨1, 0, by omega, by rw [ca_one]; rfl, by rw [ca_one]; rfl, by rw [ca_one]; rfl⟩
  · exact ⟨1, 3, by omega, by rw [ca_one]; rfl, by rw [ca_one]; rfl, by rw [ca_one]; rfl⟩

/-- Once the width-2 defect forms (`n ≥ 2`), the isolated-ON triple `(false, true, false)`
(bit index `2`) never occurs anywhere on `ℤ`. -/
theorem ca_no_010_ge2 (n : ℕ) (hn : 2 ≤ n) (j : ℤ) :
    ¬ (ca n (j - 1) = false ∧ ca n j = true ∧ ca n (j + 1) = false) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm1 : 1 ≤ m := by omega
    have hidx : n = 2 * m := by omega
    rw [hidx]
    simp only [ca_even_pos m hm1, decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · have hm1 : 1 ≤ m := by omega
    rw [hm]
    simp only [ca_odd_pos m hm1, Bool.not_eq_true', Bool.not_eq_false',
      decide_eq_true_eq, decide_eq_false_iff_not]
    omega

/-- Once the width-2 defect forms (`n ≥ 2`), the isolated-OFF triple `(true, false, true)`
(bit index `5`) never occurs anywhere on `ℤ`. -/
theorem ca_no_101_ge2 (n : ℕ) (hn : 2 ≤ n) (j : ℤ) :
    ¬ (ca n (j - 1) = true ∧ ca n j = false ∧ ca n (j + 1) = true) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm1 : 1 ≤ m := by omega
    have hidx : n = 2 * m := by omega
    rw [hidx]
    simp only [ca_even_pos m hm1, decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · have hm1 : 1 ≤ m := by omega
    rw [hm]
    simp only [ca_odd_pos m hm1, Bool.not_eq_true', Bool.not_eq_false',
      decide_eq_true_eq, decide_eq_false_iff_not]
    omega

/-- Generic Wolfram ECA rule `code` update on `(l, c, r)`. -/
def ruleOf (code : ℕ) (l c r : Bool) : Bool :=
  code.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Full-lattice single-seed evolution of Wolfram ECA `code` on `ℤ`. -/
def caRule (code : ℕ) : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => ruleOf code (caRule code n (j - 1)) (caRule code n j) (caRule code n (j + 1))

/-- Singleton single-seed equivalence class of Rule 47: because all 8 triples occur in
generations `n = 0, 1`, a Wolfram rule `code < 256` generates the exact same space-time
evolution on `ℤ` as Rule 47 if and only if `code = 47`. -/
theorem caRule_eq_ca_iff (code : ℕ) (hcode : code < 256) :
    (∀ n : ℕ, ∀ j : ℤ, caRule code n j = ca n j) ↔ code = 47 := by
  constructor
  · intro heq
    have hbits : ∀ i : ℕ, i < 8 → code.testBit i = (47 : ℕ).testBit i := by
      intro i hi
      have hrep : ∃ l c r : Bool, 4 * l.toNat + 2 * c.toNat + r.toNat = i := by
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
        · exact ⟨false, false, false, rfl⟩
        · exact ⟨false, false, true, rfl⟩
        · exact ⟨false, true, false, rfl⟩
        · exact ⟨false, true, true, rfl⟩
        · exact ⟨true, false, false, rfl⟩
        · exact ⟨true, false, true, rfl⟩
        · exact ⟨true, true, false, rfl⟩
        · exact ⟨true, true, true, rfl⟩
        · omega
      rcases hrep with ⟨l, c, r, rfl⟩
      obtain ⟨n, j, _, hl, hc, hr⟩ := ca_all_triples_occur l c r
      have hstep := heq (n + 1) j
      change ruleOf code (caRule code n (j - 1)) (caRule code n j) (caRule code n (j + 1)) =
        rule47 (ca n (j - 1)) (ca n j) (ca n (j + 1)) at hstep
      rw [heq n (j - 1), heq n j, heq n (j + 1), hl, hc, hr] at hstep
      exact hstep
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · exact hbits i hi
    · have h1 : code < 2 ^ i := lt_of_lt_of_le hcode (by
        have h8 : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        omega)
      have h2 : (47 : ℕ) < 2 ^ i := lt_of_lt_of_le (by omega : 47 < 256) (by
        have h8 : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        omega)
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
  · rintro rfl n
    induction n with
    | zero =>
      intro j
      rfl
    | succ n ih =>
      intro j
      change ruleOf 47 (caRule 47 n (j - 1)) (caRule 47 n j) (caRule 47 n (j + 1)) =
        rule47 (ca n (j - 1)) (ca n j) (ca n (j + 1))
      rw [ih (j - 1), ih j, ih (j + 1)]
      rfl

/-- Wolfram ECA Rule 117 (`117 = 0b01110101`), the left-right mirror of Rule 47. -/
def rule117 (l c r : Bool) : Bool := (117 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Rule 117 is the exact left-right reflection of Rule 47. -/
theorem rule117_eq_rule47_rev (l c r : Bool) : rule117 l c r = rule47 r c l := by
  cases l <;> cases c <;> cases r <;> rfl

/-- Bi-infinite 1D evolution of Mirror Rule 117 on `ℤ` from a single ON cell at `0`. -/
def ca117 : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule117 (ca117 n (j - 1)) (ca117 n j) (ca117 n (j + 1))

/-- OFF-cell count on `[-n, n]` for Mirror Rule 117. -/
def a117 (n : ℕ) : ℕ := ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca117 n j))).card

/-- Exact spatial-reflection duality between Rule 117 and Rule 47 on all of `ℤ`. -/
theorem ca117_eq_ca_neg (n : ℕ) : ∀ j : ℤ, ca117 n j = ca n (-j) := by
  induction n with
  | zero =>
    intro j
    have hprop : (j = 0) ↔ (-j = 0) := by omega
    exact decide_eq_decide.mpr hprop
  | succ n ih =>
    intro j
    change rule117 (ca117 n (j - 1)) (ca117 n j) (ca117 n (j + 1)) =
      rule47 (ca n (-j - 1)) (ca n (-j)) (ca n (-j + 1))
    rw [rule117_eq_rule47_rev, ih (j - 1), ih j, ih (j + 1)]
    have h1 : -(j + 1) = -j - 1 := by omega
    have h2 : -(j - 1) = -j + 1 := by omega
    rw [h1, h2]

/-- Mirror Rule 117 shares the exact same OFF-cell count sequence `A266664` on `[-n, n]`. -/
theorem a117_eq_a (n : ℕ) : a117 n = a n := by
  unfold a117 a
  apply Finset.card_bij (fun j _ => -j)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [← ca117_eq_ca_neg n j]
    exact hj.2
  · intro j₁ _ j₂ _ h
    omega
  · intro j hj
    refine ⟨-j, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [ca117_eq_ca_neg n (-j), neg_neg]
    exact hj.2

/-! ### Step 8: Non-vacuity — causal-cone mirror, OEIS spot checks, sharpness, clamping traps -/

/-- One causal-cone contraction step on a list of adjacent spatial states. -/
def coneStep : List Bool → List Bool
  | l :: c :: r :: rest => rule47 l c r :: coneStep (c :: r :: rest)
  | _ => []

/-- Iterate `coneStep` `k` times. -/
def coneIter : ℕ → List Bool → List Bool
  | 0, xs => xs
  | k + 1, xs => coneIter k (coneStep xs)

/-- Generation-0 spatial slice on `[-2n, 2n]` (`4n + 1` cells, `true` only at the center `0`). -/
def initCone (n : ℕ) : List Bool :=
  List.replicate (2 * n) false ++ [true] ++ List.replicate (2 * n) false

/-- Polynomial-time computable causal-cone mirror for OFF count `a n` ($O(n^2)$ Boolean
operations, avoiding the $(2n + 1) \cdot 3^n$ tree blowup of unmemoized recursion in `ca`). -/
def a_dp (n : ℕ) : ℕ :=
  ((coneIter n (initCone n)).filter (fun b => !b)).length

/-- Specification slice `[ca m s, ca m (s + 1), ..., ca m (s + len - 1)]`. -/
def caRow (m : ℕ) (s : ℤ) : ℕ → List Bool
  | 0 => []
  | len + 1 => ca m s :: caRow m (s + 1) len

theorem caRow_append (m : ℕ) (s : ℤ) :
    ∀ len₁ len₂ : ℕ, caRow m s (len₁ + len₂) = caRow m s len₁ ++ caRow m (s + len₁) len₂
  | 0, len₂ => by simp [caRow]
  | len₁ + 1, len₂ => by
    simp only [Nat.succ_add, caRow, List.cons_append, caRow_append m (s + 1) len₁ len₂]
    have hs : s + 1 + (len₁ : ℤ) = s + ((len₁ + 1 : ℕ) : ℤ) := by omega
    rw [hs]

theorem caRow_zero_of_upper (s : ℤ) :
    ∀ len : ℕ, s + (len : ℤ) ≤ 0 → caRow 0 s len = List.replicate len false
  | 0, _ => rfl
  | len + 1, h => by
    have hs0 : ¬(s = 0) := by omega
    simp only [caRow, List.replicate_succ, ca_zero, decide_eq_false hs0]
    rw [caRow_zero_of_upper (s + 1) len (by omega)]

theorem caRow_zero_of_lower (s : ℤ) :
    ∀ len : ℕ, 1 ≤ s → caRow 0 s len = List.replicate len false
  | 0, _ => rfl
  | len + 1, h => by
    have hs0 : ¬(s = 0) := by omega
    simp only [caRow, List.replicate_succ, ca_zero, decide_eq_false hs0]
    rw [caRow_zero_of_lower (s + 1) len (by omega)]

theorem initCone_eq_caRow (n : ℕ) :
    initCone n = caRow 0 (-(2 * (n : ℤ))) (4 * n + 1) := by
  have hlen : 4 * n + 1 = 2 * n + (1 + 2 * n) := by omega
  rw [hlen, caRow_append, caRow_append]
  have hleft : caRow 0 (-(2 * (n : ℤ))) (2 * n) = List.replicate (2 * n) false :=
    caRow_zero_of_upper _ _ (by omega)
  have hmid0 : -(2 * (n : ℤ)) + ((2 * n : ℕ) : ℤ) = 0 := by omega
  have hmid1 : (0 : ℤ) + ((1 : ℕ) : ℤ) = 1 := by omega
  rw [hleft, hmid0, hmid1]
  have hcenter : caRow 0 0 1 = [true] := by simp [caRow, ca]
  have hright : caRow 0 1 (2 * n) = List.replicate (2 * n) false :=
    caRow_zero_of_lower 1 (2 * n) (by omega)
  rw [hcenter, hright, ← List.append_assoc]
  rfl

theorem coneStep_caRow (m : ℕ) :
    ∀ (len : ℕ) (s : ℤ), coneStep (caRow m s (len + 2)) = caRow (m + 1) (s + 1) len
  | 0, s => rfl
  | len + 1, s => by
    have htail := coneStep_caRow m len (s + 1)
    simp only [caRow, coneStep] at htail ⊢
    rw [htail]
    congr 1
    change rule47 (ca m s) (ca m (s + 1)) (ca m (s + 1 + 1)) =
      rule47 (ca m ((s + 1) - 1)) (ca m (s + 1)) (ca m ((s + 1) + 1))
    have hs1 : s = (s + 1) - 1 := by omega
    rw [← hs1]

theorem coneIter_caRow :
    ∀ (k m : ℕ) (s : ℤ) (len : ℕ),
      coneIter k (caRow m s (len + 2 * k)) = caRow (m + k) (s + k) len
  | 0, m, s, len => by simp [coneIter]
  | k + 1, m, s, len => by
    have hlen : len + 2 * (k + 1) = (len + 2 * k) + 2 := by omega
    rw [hlen, coneIter, coneStep_caRow]
    have hih := coneIter_caRow k (m + 1) (s + 1) len
    rw [hih]
    have hm : m + 1 + k = m + (k + 1) := by omega
    have hs : s + 1 + (k : ℤ) = s + ((k + 1 : ℕ) : ℤ) := by omega
    rw [hm, hs]

theorem filter_caRow_length (m : ℕ) :
    ∀ (len : ℕ) (s : ℤ),
      ((caRow m s len).filter (fun b => !b)).length =
        ((Finset.Icc s (s + (len : ℤ) - 1)).filter (fun j => !(ca m j))).card
  | 0, s => by
    simp [caRow]
  | len + 1, s => by
    have hins :
        Finset.Icc s (s + ((len + 1 : ℕ) : ℤ) - 1) =
          insert s (Finset.Icc (s + 1) ((s + 1) + (len : ℤ) - 1)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem :
        s ∉ (Finset.Icc (s + 1) ((s + 1) + (len : ℤ) - 1)).filter (fun j => !(ca m j)) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hins, Finset.filter_insert]
    simp only [caRow, List.filter]
    cases hca : ca m s
    · simp only [Bool.not_false, ↓reduceIte, List.length_cons,
        Finset.card_insert_of_notMem hnotmem, filter_caRow_length m len (s + 1)]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, filter_caRow_length m len (s + 1)]

/-- Formal equivalence between the computable causal-cone mirror `a_dp` and the pinned `a`. -/
theorem a_dp_eq_a (n : ℕ) : a_dp n = a n := by
  unfold a_dp a
  rw [initCone_eq_caRow]
  have hlen : 4 * n + 1 = (2 * n + 1) + 2 * n := by omega
  rw [hlen, coneIter_caRow, filter_caRow_length]
  have hm : 0 + n = n := Nat.zero_add n
  have hs : -(2 * (n : ℤ)) + (n : ℤ) = -(n : ℤ) := by omega
  have he : -(n : ℤ) + ((2 * n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
  rw [hm, hs, he]

/-- Pure kernel `rfl` check of `a_dp` against OEIS `A266664` for `n = 0..12`. -/
theorem a_dp_spot_0_to_12 :
    (List.range 13).map a_dp = [0, 1, 3, 2, 7, 2, 11, 2, 15, 2, 19, 2, 23] :=
  rfl

/-- Kernel-checked agreement of the pinned `a` with OEIS `A266664` for `n = 0..12`. -/
theorem a_spot_0_to_12 :
    (List.range 13).map a = [0, 1, 3, 2, 7, 2, 11, 2, 15, 2, 19, 2, 23] := by
  have hfun : a = a_dp := funext (fun n => (a_dp_eq_a n).symm)
  rw [hfun]
  exact a_dp_spot_0_to_12

/-- Sharpness of `1 < n` in `a_closed_form`: fails at `n = 0` (`0 ≠ -1`). -/
theorem a_closed_form_false_zero :
    (a 0 : ℚ) ≠
      (2 * (-1 : ℚ) ^ 0 * (0 : ℚ) + 2 * (0 : ℚ) - 3 * (-1 : ℚ) ^ 0 + 1) / 2 := by
  norm_num [a_zero]

/-- Sharpness of `1 < n` in `a_closed_form`: fails at `n = 1` (`1 ≠ 2`). -/
theorem a_closed_form_false_one :
    (a 1 : ℚ) ≠
      (2 * (-1 : ℚ) ^ 1 * (1 : ℚ) + 2 * (1 : ℚ) - 3 * (-1 : ℚ) ^ 1 + 1) / 2 := by
  norm_num [a_one]

/-- Sharpness of `5 < n` in `a_recurrence`: fails at `n = 4` (`7 ≠ 6`). -/
theorem a_recurrence_false_four :
    (a 4 : ℤ) ≠ 2 * (a (4 - 2) : ℤ) - (a (4 - 4) : ℤ) := by
  norm_num [a_four, a_two, a_zero]

/-- Sharpness of `5 < n` in `a_recurrence`: fails at `n = 5` (`2 ≠ 3`). -/
theorem a_recurrence_false_five :
    (a 5 : ℤ) ≠ 2 * (a (5 - 2) : ℤ) - (a (5 - 4) : ℤ) := by
  norm_num [a_five, a_three, a_one]

/-- Trap A (row-by-row light-cone zero-clamping, `PIN-C055.md` fidelity note 1):
cells outside `[-m, m]` at step `m` are forced to `false` before computing step `m + 1`. -/
def caConeClamp : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | m + 1, j =>
    let get (k : ℤ) : Bool := if -(m : ℤ) ≤ k ∧ k ≤ (m : ℤ) then caConeClamp m k else false
    if -((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + 1 : ℕ) : ℤ) then
      rule47 (get (j - 1)) (get j) (get (j + 1))
    else
      false

/-- OFF-cell count on `[-n, n]` under Trap A (light-cone zero-clamping). -/
def aConeClamp (n : ℕ) : ℕ :=
  ((List.range (2 * n + 1)).filter (fun i => !(caConeClamp n ((i : ℤ) - (n : ℤ))))).length

/-- Kernel `rfl` confirmation of Trap A (`PIN-C055.md` fidelity note 1):
step-clamped zero exterior produces `11001` (`2` OFF cells) at `n = 2`, whereas true
`ℤ`-evolution produces `00011` (`a 2 = 3`). -/
theorem aConeClamp_two_eq_two : aConeClamp 2 = 2 ∧ aConeClamp 2 ≠ a 2 := by
  have h : aConeClamp 2 = 2 := rfl
  refine ⟨h, ?_⟩
  rw [h, a_two]
  omega

/-- Trap B (fixed-box `[-R, R]` zero-clamping, `PIN-C055.md` fidelity note 1):
evolves on a fixed window `[-R, R]` with cells outside `[-R, R]` clamped to `false`. -/
def caBoxClamp (R : ℕ) : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | m + 1, j =>
    let get (k : ℤ) : Bool := if -(R : ℤ) ≤ k ∧ k ≤ (R : ℤ) then caBoxClamp R m k else false
    if -(R : ℤ) ≤ j ∧ j ≤ (R : ℤ) then
      rule47 (get (j - 1)) (get j) (get (j + 1))
    else
      false

/-- OFF-cell count on `[-n, n]` under Trap B (fixed-box `[-n, n]` zero-clamping). -/
def aBoxClamp (n : ℕ) : ℕ :=
  ((List.range (2 * n + 1)).filter (fun i => !(caBoxClamp n n ((i : ℤ) - (n : ℤ))))).length

/-- Kernel `rfl` confirmation of Trap B (`PIN-C055.md` fidelity note 1):
fixed-box `[-2, 2]` zero-clamping produces `10011` (`2` OFF cells) at `n = 2`, whereas true
`ℤ`-evolution produces `00011` (`a 2 = 3`). -/
theorem aBoxClamp_two_eq_two : aBoxClamp 2 = 2 ∧ aBoxClamp 2 ≠ a 2 := by
  have h : aBoxClamp 2 = 2 := rfl
  refine ⟨h, ?_⟩
  rw [h, a_two]
  omega

end Mathproofs.A266664
