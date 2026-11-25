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
# Seam B Entry C052 (OEIS A266256): Colin Barker Rule 11 ON-Cell Conjecture Bundle

Formalizes and proves Colin Barker's three-part conjecture bundle on `OEIS A266256`
(`%F` lines 16–20, Dec 27 2015 and Apr 14 2019; authored by Robert Price, Dec 25 2015)
together with the explicit Rule 11 bit-index equivalence (`rule11_eq_testBit`) and
initial value (`a 0 = 1`), against the frozen target contract `PIN-C052.md` v1
(`sha256: f6e0818fe636e3d52e04e4965d5750c5c7a169ebfe1229157a5a25d7efaf88c0`,
`Statement.lean sha256: 84b6e2e73ccc2949445ae7968474734066a0e20cf5e8437f80138aabb9c1ac73`,
`delta_vs_source: NONE`), following the 2-step right-edge glider + alternating-exterior
route in `SCOPING-C052.md` (§2.2, §5.1–§5.2):

1. **Wolfram Rule 11 truth table and algebraic reduction (`rule11_eq_testBit`, `rule11_eq`,
   `rule11_not_symm`)**: proves equivalence of the explicit 8-branch truth table with
   bit `4*l + 2*c + r` of `11 = 0b00001011` and the minimal Boolean normal form
   `(!l) && (!c || r)` by pure kernel reduction (`rfl`).
2. **Initial value and generation `n = 1` (`ca_zero`, `a_zero`, `ca_one`)**: proves
   `a 0 = 1` and establishes `ca 1 j = decide (j ≠ 0 ∧ j ≠ 1)` across all of `ℤ`.
3. **2-step right-edge glider + alternating-exterior invariant on `ℤ`
   (`ca_step_odd_to_even`, `ca_step_even_to_odd`, `ca_odd_even`, `ca_odd`, `ca_even_pos`,
   `ca_eq_xor`)**: proves by induction on `m : ℕ` that
   `ca (2*m + 1) j = decide (j ≠ 2*m ∧ j ≠ 2*m + 1)` and
   `ca (2*m + 2) j = decide (j = 2*m + 1 ∨ j = 2*m + 2)` across all `j : ℤ`, evolving
   globally on `ℤ` before restricting to `[-n, n]` inside `a n`.
4. **Window counts, closed form, and 4-step recurrence (`a_even_pos`, `a_odd`,
   `a_closed_form`, `a_recurrence`)**: deduces `a (2*m) = 2` (`m ≥ 1`),
   `a (2*m + 1) = 4*m + 1` (`m ≥ 0`), Barker's cleared-denominator closed form for
   `0 < n`, and the 4-step linear recurrence `a n = 2 * a (n - 2) - a (n - 4)` for `4 < n`.
5. **Rational ordinary generating function and bundle (`a_gf`, `c052_a266256_bundle`,
   `a_gf_denom_isUnit`, `a_gf_unit_inv`)**: rewrites
   `((1 - X)^2 * (1 + X)^2) * F = F - 2 * (X^2 * F) + X^4 * F` in `PowerSeries ℚ`,
   proves equality with `1 + X + 3 * X^3 - X^4` coefficientwise via `PowerSeries.ext`
   and `PowerSeries.coeff_X_pow_mul'`, and establishes unit invertibility of the denominator.
6. **Structural and non-vacuity extensions (`a_add_aOff`, `ca_no_101`,
   `caRule_eq_ca`, `caRule_equiv_class`, `a_dp_eq_a`, `a_dp_spot_0_to_12`,
   `a_spot_0_to_12`, `a_closed_form_false_zero`, `a_recurrence_false_four`,
   `aConeClamp_two_eq_three`, `aBoxClamp_trap`)**.
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

/-! ### Step 1: Rule 11 bit-index equivalence and algebraic characterization -/

theorem rule11_eq_testBit (l c r : Bool) :
    rule11 l c r = Nat.testBit 11 ((if l then 4 else 0) + (if c then 2 else 0) + (if r then 1 else 0)) := by
  cases l <;> cases c <;> cases r <;> rfl

/-- Minimal Boolean normal form of Rule 11: `rule11 l c r = (!l) && (!c || r)`. -/
theorem rule11_eq (l c r : Bool) : rule11 l c r = ((!l) && (!c || r)) := by
  cases l <;> cases c <;> cases r <;> rfl

/-- Rule 11 breaks left-right reflection symmetry (`rule11 0 0 1 = true ≠ false = rule11 1 0 0`). -/
theorem rule11_not_symm : rule11 false false true ≠ rule11 true false false := by
  intro h
  cases h

/-! ### Step 2: Base value `a 0 = 1` and generation `n = 1` on `ℤ` -/

theorem ca_zero (j : ℤ) : ca 0 j = decide (j = 0) :=
  rfl

theorem a_zero : a 0 = 1 := by
  unfold a
  have hfilter :
      (Finset.Icc (-(0 : ℕ) : ℤ) (0 : ℕ)).filter (fun j => ca 0 j = true) = {(0 : ℤ)} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, Nat.cast_zero, neg_zero]
    constructor
    · intro ⟨⟨hlo, hhi⟩, _⟩
      omega
    · rintro rfl
      exact ⟨⟨le_rfl, le_rfl⟩, rfl⟩
  rw [hfilter, Finset.card_singleton]

/-- Generation `n = 1` on all of `ℤ`: only `{0, 1}` are OFF (`false`), while every other
cell on `ℤ` (including the infinite exterior `|j| > 1`) is ON (`true`). -/
theorem ca_one (j : ℤ) : ca 1 j = decide (j ≠ 0 ∧ j ≠ 1) := by
  change rule11 (decide (j - 1 = 0)) (decide (j = 0)) (decide (j + 1 = 0)) =
    decide (j ≠ 0 ∧ j ≠ 1)
  rw [rule11_eq]
  by_cases h0 : j = 0
  · subst h0
    rfl
  · by_cases h1 : j = 1
    · subst h1
      rfl
    · have hl : ¬(j - 1 = 0) := by omega
      have hrhs : j ≠ 0 ∧ j ≠ 1 := ⟨h0, h1⟩
      rw [decide_eq_false hl, decide_eq_false h0, decide_eq_true hrhs]
      simp

/-! ### Step 3: Coupled 2-step right-edge glider + alternating-exterior invariant on `ℤ` -/

/-- Odd-to-even transition on `ℤ`: a 2-cell OFF defect `{n - 1, n}` in an ON background
advances rightward by `1` to a 2-cell ON defect `{n, n + 1}` in an OFF background. -/
theorem ca_step_odd_to_even (n : ℕ)
    (h : ∀ j : ℤ, ca n j = decide (j ≠ (n : ℤ) - 1 ∧ j ≠ (n : ℤ))) :
    ∀ j : ℤ, ca (n + 1) j = decide (j = (n : ℤ) ∨ j = (n : ℤ) + 1) := by
  intro j
  change rule11 (ca n (j - 1)) (ca n j) (ca n (j + 1)) =
    decide (j = (n : ℤ) ∨ j = (n : ℤ) + 1)
  rw [rule11_eq, h (j - 1), h j, h (j + 1)]
  by_cases hjn : j = (n : ℤ)
  · subst hjn
    rw [decide_eq_false (by omega : ¬(((n : ℤ) - 1 ≠ (n : ℤ) - 1) ∧ ((n : ℤ) - 1 ≠ (n : ℤ)))),
        decide_eq_false (by omega : ¬(((n : ℤ) ≠ (n : ℤ) - 1) ∧ ((n : ℤ) ≠ (n : ℤ)))),
        decide_eq_true (by omega : ((n : ℤ) + 1 ≠ (n : ℤ) - 1) ∧ ((n : ℤ) + 1 ≠ (n : ℤ))),
        decide_eq_true (Or.inl rfl)]
    rfl
  · by_cases hjn1 : j = (n : ℤ) + 1
    · subst hjn1
      rw [decide_eq_false (by omega : ¬((((n : ℤ) + 1 - 1 ≠ (n : ℤ) - 1) ∧ ((n : ℤ) + 1 - 1 ≠ (n : ℤ))))),
          decide_eq_true (by omega : ((n : ℤ) + 1 ≠ (n : ℤ) - 1) ∧ ((n : ℤ) + 1 ≠ (n : ℤ))),
          decide_eq_true (by omega : ((n : ℤ) + 1 + 1 ≠ (n : ℤ) - 1) ∧ ((n : ℤ) + 1 + 1 ≠ (n : ℤ))),
          decide_eq_true (Or.inr rfl)]
      rfl
    · have hl : (j - 1 ≠ (n : ℤ) - 1) ∧ (j - 1 ≠ (n : ℤ)) := by omega
      have hrhs : ¬(j = (n : ℤ) ∨ j = (n : ℤ) + 1) := by omega
      rw [decide_eq_true hl, decide_eq_false hrhs]
      rfl

/-- Even-to-odd transition on `ℤ`: a 2-cell ON defect `{n - 1, n}` in an OFF background
advances rightward by `1` to a 2-cell OFF defect `{n, n + 1}` in an ON background. -/
theorem ca_step_even_to_odd (n : ℕ)
    (h : ∀ j : ℤ, ca n j = decide (j = (n : ℤ) - 1 ∨ j = (n : ℤ))) :
    ∀ j : ℤ, ca (n + 1) j = decide (j ≠ (n : ℤ) ∧ j ≠ (n : ℤ) + 1) := by
  intro j
  change rule11 (ca n (j - 1)) (ca n j) (ca n (j + 1)) =
    decide (j ≠ (n : ℤ) ∧ j ≠ (n : ℤ) + 1)
  rw [rule11_eq, h (j - 1), h j, h (j + 1)]
  by_cases hjn : j = (n : ℤ)
  · subst hjn
    rw [decide_eq_true (by omega : (n : ℤ) - 1 = (n : ℤ) - 1 ∨ (n : ℤ) - 1 = (n : ℤ)),
        decide_eq_false (by omega : ¬((n : ℤ) ≠ (n : ℤ) ∧ (n : ℤ) ≠ (n : ℤ) + 1))]
    rfl
  · by_cases hjn1 : j = (n : ℤ) + 1
    · subst hjn1
      rw [decide_eq_true (by omega : (n : ℤ) + 1 - 1 = (n : ℤ) - 1 ∨ (n : ℤ) + 1 - 1 = (n : ℤ)),
          decide_eq_false (by omega : ¬((n : ℤ) + 1 ≠ (n : ℤ) ∧ (n : ℤ) + 1 ≠ (n : ℤ) + 1))]
      rfl
    · by_cases hjm : j = (n : ℤ) - 1
      · subst hjm
        rw [decide_eq_false (by omega : ¬((n : ℤ) - 1 - 1 = (n : ℤ) - 1 ∨ (n : ℤ) - 1 - 1 = (n : ℤ))),
            decide_eq_true (by omega : (n : ℤ) - 1 = (n : ℤ) - 1 ∨ (n : ℤ) - 1 = (n : ℤ)),
            decide_eq_true (by omega : (n : ℤ) - 1 + 1 = (n : ℤ) - 1 ∨ (n : ℤ) - 1 + 1 = (n : ℤ)),
            decide_eq_true (by omega : (n : ℤ) - 1 ≠ (n : ℤ) ∧ (n : ℤ) - 1 ≠ (n : ℤ) + 1)]
        rfl
      · have hl : ¬(j - 1 = (n : ℤ) - 1 ∨ j - 1 = (n : ℤ)) := by omega
        have hc : ¬(j = (n : ℤ) - 1 ∨ j = (n : ℤ)) := by omega
        have hrhs : j ≠ (n : ℤ) ∧ j ≠ (n : ℤ) + 1 := by omega
        rw [decide_eq_false hl, decide_eq_false hc, decide_eq_true hrhs]
        simp

/-- Coupled global `ℤ`-invariant for all `m : ℕ`:
odd generations `2m + 1` are `true` everywhere except `{2m, 2m + 1}`;
even generations `2m + 2` are `false` everywhere except `{2m + 1, 2m + 2}`. -/
theorem ca_odd_even (m : ℕ) :
    (∀ j : ℤ, ca (2 * m + 1) j = decide (j ≠ 2 * (m : ℤ) ∧ j ≠ 2 * (m : ℤ) + 1)) ∧
    (∀ j : ℤ, ca (2 * m + 2) j = decide (j = 2 * (m : ℤ) + 1 ∨ j = 2 * (m : ℤ) + 2)) := by
  induction m with
  | zero =>
    have h1 : ∀ j : ℤ, ca 1 j = decide (j ≠ (1 : ℕ) - 1 ∧ j ≠ (1 : ℕ)) := by
      intro j
      simpa using ca_one j
    have h2 := ca_step_odd_to_even 1 h1
    refine ⟨?_, ?_⟩
    · intro j; simpa using ca_one j
    · intro j; simpa using h2 j
  | succ m ih =>
    have heven : ∀ j : ℤ, ca (2 * m + 2) j =
        decide (j = ((2 * m + 2 : ℕ) : ℤ) - 1 ∨ j = ((2 * m + 2 : ℕ) : ℤ)) := by
      intro j
      rw [ih.2 j]
      push_cast
      ring_nf
    have hodd_raw := ca_step_even_to_odd (2 * m + 2) heven
    have hodd : ∀ j : ℤ, ca (2 * (m + 1) + 1) j =
        decide (j ≠ 2 * ((m + 1 : ℕ) : ℤ) ∧ j ≠ 2 * ((m + 1 : ℕ) : ℤ) + 1) := by
      intro j
      have hidx : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by omega
      rw [hidx, hodd_raw j]
      push_cast
      ring_nf
    have hodd' : ∀ j : ℤ, ca (2 * (m + 1) + 1) j =
        decide (j ≠ ((2 * (m + 1) + 1 : ℕ) : ℤ) - 1 ∧ j ≠ ((2 * (m + 1) + 1 : ℕ) : ℤ)) := by
      intro j
      rw [hodd j]
      congr 1
      push_cast
      ring_nf
    have heven_next_raw := ca_step_odd_to_even (2 * (m + 1) + 1) hodd'
    have heven_next : ∀ j : ℤ, ca (2 * (m + 1) + 2) j =
        decide (j = 2 * ((m + 1 : ℕ) : ℤ) + 1 ∨ j = 2 * ((m + 1 : ℕ) : ℤ) + 2) := by
      intro j
      have hidx : 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 := by omega
      rw [hidx, heven_next_raw j]
      push_cast
      ring_nf
    exact ⟨hodd, heven_next⟩

theorem ca_odd (m : ℕ) (j : ℤ) :
    ca (2 * m + 1) j = decide (j ≠ 2 * (m : ℤ) ∧ j ≠ 2 * (m : ℤ) + 1) :=
  (ca_odd_even m).1 j

theorem ca_even_pos (m : ℕ) (hm : 1 ≤ m) (j : ℤ) :
    ca (2 * m) j = decide (j = 2 * (m : ℤ) - 1 ∨ j = 2 * (m : ℤ)) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 1 := ⟨m - 1, by omega⟩
  have h := (ca_odd_even k).2 j
  have hidx : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [hidx, h]
  congr 1
  push_cast
  ring_nf

/-- Unified global characterization for every `n ≥ 1` and `j ∈ ℤ`:
`ca n j` is the XOR of the generation parity (`Odd n`) with the 2-cell right-moving
defect indicator `j ∈ {n - 1, n}`. -/
theorem ca_eq_xor (n : ℕ) (hn : 1 ≤ n) (j : ℤ) :
    ca n j = xor (decide (Odd n)) (decide (j = (n : ℤ) - 1 ∨ j = (n : ℤ))) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hm : 1 ≤ m := by omega
    have hnot : ¬ Odd (m + m) := by
      rintro ⟨t, ht⟩
      omega
    rw [show m + m = 2 * m by omega] at hnot ⊢
    rw [ca_even_pos m hm j, decide_eq_false hnot]
    simp only [Bool.false_xor]
    push_cast
    rfl
  · have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
    rw [ca_odd m j, decide_eq_true hodd]
    by_cases hdef : j = ((2 * m + 1 : ℕ) : ℤ) - 1 ∨ j = ((2 * m + 1 : ℕ) : ℤ)
    · rw [decide_eq_true hdef, decide_eq_false (by push_cast at hdef; omega)]
      rfl
    · rw [decide_eq_false hdef, decide_eq_true (by push_cast at hdef; omega)]
      rfl

/-! ### Step 4: Window counting on `[-n, n]` and Barker's closed form (`0 < n`) -/

/-- Exact ON-cell count at positive even generations: `a (2m) = 2` for all `m ≥ 1`. -/
theorem a_even_pos (m : ℕ) (hm : 1 ≤ m) : a (2 * m) = 2 := by
  unfold a
  have hfilter :
      (Finset.Icc (-((2 * m : ℕ) : ℤ)) ((2 * m : ℕ) : ℤ)).filter (fun j => ca (2 * m) j = true) =
        ({2 * (m : ℤ) - 1, 2 * (m : ℤ)} : Finset ℤ) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      ca_even_pos m hm, decide_eq_true_eq]
    push_cast
    omega
  rw [hfilter, Finset.card_pair (by omega : 2 * (m : ℤ) - 1 ≠ 2 * (m : ℤ))]

/-- Exact ON-cell count at odd generations: `a (2m + 1) = 4m + 1` for all `m ≥ 0`. -/
theorem a_odd (m : ℕ) : a (2 * m + 1) = 4 * m + 1 := by
  unfold a
  have hfilter :
      (Finset.Icc (-((2 * m + 1 : ℕ) : ℤ)) ((2 * m + 1 : ℕ) : ℤ)).filter
          (fun j => ca (2 * m + 1) j = true) =
        Finset.Icc (-((2 * m + 1 : ℕ) : ℤ)) (2 * (m : ℤ) - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, ca_odd m, decide_eq_true_eq]
    push_cast
    omega
  rw [hfilter, Int.card_Icc]
  push_cast
  omega

theorem a_one : a 1 = 1 := by
  simpa using a_odd 0

theorem a_two : a 2 = 2 := by
  simpa using a_even_pos 1 (by omega)

theorem a_three : a 3 = 5 := by
  simpa using a_odd 1

theorem a_four : a 4 = 2 := by
  simpa using a_even_pos 2 (by omega)

theorem a_closed_form (n : ℕ) (hn : 0 < n) :
    2 * (a n : ℤ) = -2 * ((-1 : ℤ) ^ n - 1) * (n : ℤ) + 3 * (-1 : ℤ) ^ n + 1 := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hm : 1 ≤ m := by omega
    rw [show m + m = 2 * m by omega, a_even_pos m hm]
    have hpow : (-1 : ℤ) ^ (2 * m) = 1 := by
      rw [pow_mul]
      norm_num
    rw [hpow]
    push_cast
    ring
  · rw [a_odd m]
    have hpow : (-1 : ℤ) ^ (2 * m + 1) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    rw [hpow]
    push_cast
    ring

/-! ### Step 5: Four-step linear recurrence (`4 < n`) -/

theorem a_recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hm : 3 ≤ m := by omega
    have h0 : m + m = 2 * m := by omega
    have h2 : 2 * m - 2 = 2 * (m - 1) := by omega
    have h4 : 2 * m - 4 = 2 * (m - 2) := by omega
    rw [h0, h2, h4, a_even_pos m (by omega), a_even_pos (m - 1) (by omega),
        a_even_pos (m - 2) (by omega)]
    norm_num
  · have hm : 2 ≤ m := by omega
    have h2 : 2 * m + 1 - 2 = 2 * (m - 1) + 1 := by omega
    have h4 : 2 * m + 1 - 4 = 2 * (m - 2) + 1 := by omega
    rw [h2, h4, a_odd m, a_odd (m - 1), a_odd (m - 2)]
    omega

/-! ### Step 6: Rational ordinary generating function in `PowerSeries ℚ` and C052 bundle -/

theorem a_gf :
    ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 * (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) *
        PowerSeries.mk (fun n => (a n : ℚ)) =
      1 + (PowerSeries.X : PowerSeries ℚ) + 3 * (PowerSeries.X : PowerSeries ℚ) ^ 3 -
        (PowerSeries.X : PowerSeries ℚ) ^ 4 := by
  let X : PowerSeries ℚ := PowerSeries.X
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hlhs : ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) * F =
      F - 2 * (X ^ 2 * F) + X ^ 4 * F := by ring
  change ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) * F =
      1 + X + 3 * X ^ 3 - X ^ 4
  rw [hlhs]
  apply PowerSeries.ext
  intro n
  dsimp only [X, F]
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_one, PowerSeries.coeff_X]
  rcases n with _ | _ | _ | _ | _ | k
  · norm_num [a_zero]
  · norm_num [a_one]
  · norm_num [a_zero, a_two]
  · norm_num [a_one, a_three]
  · norm_num [a_zero, a_two, a_four]
  · have hrec : (a (k + 5) : ℤ) = 2 * (a (k + 3) : ℤ) - (a (k + 1) : ℤ) := by
      simpa using a_recurrence (k + 5) (by omega)
    have hrec_q : (a (k + 5) : ℚ) = 2 * (a (k + 3) : ℚ) - (a (k + 1) : ℚ) := by
      exact_mod_cast hrec
    have h2 : 2 ≤ k + 5 := by omega
    have h4 : 4 ≤ k + 5 := by omega
    have hne0 : k + 5 ≠ 0 := by omega
    have hne1 : k + 5 ≠ 1 := by omega
    have hne3 : k + 5 ≠ 3 := by omega
    have hne4 : k + 5 ≠ 4 := by omega
    simp only [h2, h4, hne0, hne1, hne3, hne4, ↓reduceIte,
      show k + 5 - 2 = k + 3 by omega, show k + 5 - 4 = k + 1 by omega]
    linarith

theorem c052_a266256_bundle :
    a 0 = 1 ∧
      (∀ n : ℕ, 0 < n → 2 * (a n : ℤ) = -2 * ((-1 : ℤ) ^ n - 1) * (n : ℤ) + 3 * (-1 : ℤ) ^ n + 1) ∧
      (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
      (((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 * (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) *
          PowerSeries.mk (fun n => (a n : ℚ)) =
        1 + (PowerSeries.X : PowerSeries ℚ) + 3 * (PowerSeries.X : PowerSeries ℚ) ^ 3 -
          (PowerSeries.X : PowerSeries ℚ) ^ 4) :=
  ⟨a_zero, a_closed_form, a_recurrence, a_gf⟩

/-! ### Step 7: Unit invertibility, OFF-cell complement, and Rule 43 equivalence -/

/-- The cleared denominator `(1 - X)^2 * (1 + X)^2` has constant coefficient `1 ≠ 0` and
is therefore a unit in `PowerSeries ℚ`. -/
theorem a_gf_denom_isUnit :
    IsUnit ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
      (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_mul, map_pow, map_sub, map_add, map_one, PowerSeries.constantCoeff_X]
  norm_num

/-- Lossless inverse-series form of `a_gf` in `PowerSeries ℚ`. -/
theorem a_gf_unit_inv :
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + (PowerSeries.X : PowerSeries ℚ) + 3 * (PowerSeries.X : PowerSeries ℚ) ^ 3 -
        (PowerSeries.X : PowerSeries ℚ) ^ 4) *
      ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
        (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2)⁻¹ := by
  have hcc : PowerSeries.constantCoeff
      ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
        (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) ≠ 0 := by
    simp only [map_mul, map_pow, map_sub, map_add, map_one, PowerSeries.constantCoeff_X]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel
    ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
      (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) hcc
  calc
    PowerSeries.mk (fun n => (a n : ℚ))
        = PowerSeries.mk (fun n => (a n : ℚ)) *
            (((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
                (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) *
              ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
                (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2)⁻¹) := by
          rw [hinv, mul_one]
    _ = (((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
            (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) *
          PowerSeries.mk (fun n => (a n : ℚ))) *
          ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
            (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2)⁻¹ := by
          ring
    _ = (1 + (PowerSeries.X : PowerSeries ℚ) + 3 * (PowerSeries.X : PowerSeries ℚ) ^ 3 -
          (PowerSeries.X : PowerSeries ℚ) ^ 4) *
        ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
          (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2)⁻¹ := by
          rw [a_gf]

/-- Companion OFF-cell count on `[-n, n]` (`OEIS A266258`). -/
def aOff (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j = false)).card

/-- Exact ON/OFF complement law on the active window `[-n, n]`: `a n + aOff n = 2n + 1`. -/
theorem a_add_aOff (n : ℕ) : a n + aOff n = 2 * n + 1 := by
  unfold a aOff
  have hdisj :
      Disjoint
        ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j = true))
        ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j = false)) := by
    rw [Finset.disjoint_filter]
    intro j _ h1 h2
    rw [h2] at h1
    exact Bool.false_ne_true h1
  have hunion :
      ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j = true)) ∪
        ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j = false)) =
      Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter]
    cases ca n j <;> simp
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Int.card_Icc]
  omega

/-- The isolated-zero neighborhood `(true, false, true)` (bit index 5) never occurs in any
generation of Rule 11 evolved on `ℤ` from a single ON cell at `j = 0`. -/
theorem ca_no_101 (n : ℕ) (j : ℤ) :
    ¬ (ca n (j - 1) = true ∧ ca n j = false ∧ ca n (j + 1) = true) := by
  rcases n with _ | n
  · simp only [ca_zero, decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hm1 : 1 ≤ m := by omega
      have hidx : n + 1 = 2 * m := by omega
      rw [hidx]
      simp only [ca_even_pos m hm1, decide_eq_true_eq, decide_eq_false_iff_not]
      omega
    · rw [hm]
      simp only [ca_odd m, decide_eq_true_eq, decide_eq_false_iff_not]
      omega

/-- Generic Wolfram ECA rule `code` update on `(l, c, r)`. -/
def ruleOf (code : ℕ) (l c r : Bool) : Bool :=
  Nat.testBit code ((if l then 4 else 0) + (if c then 2 else 0) + (if r then 1 else 0))

/-- Full-lattice single-seed evolution of Wolfram ECA `code` on `ℤ`. -/
def caRule (code : ℕ) : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => ruleOf code (caRule code n (j - 1)) (caRule code n j) (caRule code n (j + 1))

/-- Any Wolfram rule agreeing with Rule 11 on bits `{0, 1, 2, 3, 4, 6, 7}` produces the exact
same single-seed space-time evolution on `ℤ`, because bit `5` `(1, 0, 1)` is never queried. -/
theorem caRule_eq_ca (code : ℕ)
    (h0 : Nat.testBit code 0 = true)
    (h1 : Nat.testBit code 1 = true)
    (h2 : Nat.testBit code 2 = false)
    (h3 : Nat.testBit code 3 = true)
    (h4 : Nat.testBit code 4 = false)
    (h6 : Nat.testBit code 6 = false)
    (h7 : Nat.testBit code 7 = false) :
    ∀ n : ℕ, ∀ j : ℤ, caRule code n j = ca n j := by
  intro n
  induction n with
  | zero =>
    intro j
    rfl
  | succ n ih =>
    intro j
    change ruleOf code (caRule code n (j - 1)) (caRule code n j) (caRule code n (j + 1)) =
      rule11 (ca n (j - 1)) (ca n j) (ca n (j + 1))
    rw [ih (j - 1), ih j, ih (j + 1)]
    have hno := ca_no_101 n j
    generalize hl : ca n (j - 1) = l at hno ⊢
    generalize hc : ca n j = c at hno ⊢
    generalize hr : ca n (j + 1) = r at hno ⊢
    cases l <;> cases c <;> cases r
    · simpa [ruleOf, rule11] using h0
    · simpa [ruleOf, rule11] using h1
    · simpa [ruleOf, rule11] using h2
    · simpa [ruleOf, rule11] using h3
    · simpa [ruleOf, rule11] using h4
    · exact False.elim (hno ⟨rfl, rfl, rfl⟩)
    · simpa [ruleOf, rule11] using h6
    · simpa [ruleOf, rule11] using h7

/-- The 2-rule single-seed equivalence class noted on `OEIS A266253`:
Rules `11` (`0b00001011`) and `43` (`0b00101011`) produce the exact same space-time
diagram on all of `ℤ`. -/
theorem caRule_equiv_class (code : ℕ) (hcode : code ∈ ([11, 43] : List ℕ)) :
    ∀ n : ℕ, ∀ j : ℤ, caRule code n j = ca n j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
  rcases hcode with rfl | rfl <;>
    exact caRule_eq_ca _ rfl rfl rfl rfl rfl rfl rfl

/-! ### Step 8: Non-vacuity — causal-cone mirror, OEIS spot checks, sharpness, clamping traps -/

/-- One causal-cone contraction step on a list of adjacent spatial states. -/
def coneStep : List Bool → List Bool
  | l :: c :: r :: rest => rule11 l c r :: coneStep (c :: r :: rest)
  | _ => []

/-- Iterate `coneStep` `k` times. -/
def coneIter : ℕ → List Bool → List Bool
  | 0, xs => xs
  | k + 1, xs => coneIter k (coneStep xs)

/-- Generation-0 spatial slice on `[-2n, 2n]` (`4n + 1` cells, `true` only at the center `0`). -/
def initCone (n : ℕ) : List Bool :=
  List.replicate (2 * n) false ++ [true] ++ List.replicate (2 * n) false

/-- Polynomial-time computable causal-cone mirror for `a n` ($O(n^2)$ Boolean operations,
avoiding the $(2n + 1) \cdot 3^n$ tree blowup of unmemoized recursion in `ca`). -/
def a_dp (n : ℕ) : ℕ :=
  ((coneIter n (initCone n)).filter (fun b => b)).length

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
    change rule11 (ca m s) (ca m (s + 1)) (ca m (s + 1 + 1)) =
      rule11 (ca m ((s + 1) - 1)) (ca m (s + 1)) (ca m ((s + 1) + 1))
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
      ((caRow m s len).filter (fun b => b)).length =
        ((Finset.Icc s (s + (len : ℤ) - 1)).filter (fun j => ca m j = true)).card
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
        s ∉ (Finset.Icc (s + 1) ((s + 1) + (len : ℤ) - 1)).filter (fun j => ca m j = true) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hins, Finset.filter_insert]
    simp only [caRow, List.filter]
    cases hca : ca m s
    · simp only [Bool.false_eq_true, ↓reduceIte, filter_caRow_length m len (s + 1)]
    · simp only [↓reduceIte, List.length_cons,
        Finset.card_insert_of_notMem hnotmem, filter_caRow_length m len (s + 1)]

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

/-- Pure kernel `rfl` check of `a_dp` against OEIS `A266256` for `n = 0..12`. -/
theorem a_dp_spot_0_to_12 :
    (List.range 13).map a_dp = [1, 1, 2, 5, 2, 9, 2, 13, 2, 17, 2, 21, 2] :=
  rfl

/-- Kernel-checked agreement of the pinned `a` with OEIS `A266256` for `n = 0..12`. -/
theorem a_spot_0_to_12 :
    (List.range 13).map a = [1, 1, 2, 5, 2, 9, 2, 13, 2, 17, 2, 21, 2] := by
  have hfun : a = a_dp := funext (fun n => (a_dp_eq_a n).symm)
  rw [hfun]
  exact a_dp_spot_0_to_12

/-- Sharpness of `0 < n` in `a_closed_form`: fails at `n = 0` (`2 ≠ 4`). -/
theorem a_closed_form_false_zero :
    2 * (a 0 : ℤ) ≠ -2 * ((-1 : ℤ) ^ 0 - 1) * (0 : ℤ) + 3 * (-1 : ℤ) ^ 0 + 1 := by
  norm_num [a_zero]

/-- Sharpness of `4 < n` in `a_recurrence`: fails at `n = 4` (`2 ≠ 3`). -/
theorem a_recurrence_false_four :
    (a 4 : ℤ) ≠ 2 * (a (4 - 2) : ℤ) - (a (4 - 4) : ℤ) := by
  norm_num [a_four, a_two, a_zero]

/-- Trap A (row-by-row light-cone zero-clamping, `PIN-C052.md` fidelity note 1):
cells outside `[-m, m]` at step `m` are forced to `false` before computing step `m + 1`. -/
def caConeClamp : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | m + 1, j =>
    let get (k : ℤ) : Bool := if -(m : ℤ) ≤ k ∧ k ≤ (m : ℤ) then caConeClamp m k else false
    if -((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + 1 : ℕ) : ℤ) then
      rule11 (get (j - 1)) (get j) (get (j + 1))
    else
      false

/-- ON-cell count on `[-n, n]` under Trap A (light-cone zero-clamping). -/
def aConeClamp (n : ℕ) : ℕ :=
  ((List.range (2 * n + 1)).filter (fun i => caConeClamp n ((i : ℤ) - (n : ℤ)))).length

/-- Kernel `rfl` confirmation of Trap A (`PIN-C052.md` fidelity note 1):
cone zero-clamping produces `10011` (`3` ON cells) at `n = 2`, whereas true `ℤ`-evolution
produces `00011` (`a 2 = 2`). -/
theorem aConeClamp_two_eq_three : aConeClamp 2 = 3 ∧ aConeClamp 2 ≠ a 2 := by
  have h : aConeClamp 2 = 3 := rfl
  refine ⟨h, ?_⟩
  rw [h, a_two]
  omega

/-- Trap B (fixed-box `[-R, R]` zero-clamping, `PIN-C052.md` fidelity note 1):
evolves on a fixed window `[-R, R]` with cells outside `[-R, R]` clamped to `false`. -/
def caBoxClamp (R : ℕ) : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | m + 1, j =>
    let get (k : ℤ) : Bool := if -(R : ℤ) ≤ k ∧ k ≤ (R : ℤ) then caBoxClamp R m k else false
    if -(R : ℤ) ≤ j ∧ j ≤ (R : ℤ) then
      rule11 (get (j - 1)) (get j) (get (j + 1))
    else
      false

/-- ON-cell count on `[-n, n]` under Trap B (fixed-box `[-n, n]` zero-clamping). -/
def aBoxClamp (n : ℕ) : ℕ :=
  ((List.range (2 * n + 1)).filter (fun i => caBoxClamp n n ((i : ℤ) - (n : ℤ)))).length

/-- Kernel `rfl` confirmation of Trap B (`PIN-C052.md` fidelity note 1):
fixed-box clamping corrupts the bit profile already at `n = 2` (`10010` vs `00011` at `j = -2`)
and yields count `3 ≠ 5 = a 3` at `n = 3`. -/
theorem aBoxClamp_trap :
    (caBoxClamp 2 2 (-2) = true ∧ ca 2 (-2) = false) ∧
    (aBoxClamp 3 = 3 ∧ aBoxClamp 3 ≠ a 3) := by
  have hbit_box : caBoxClamp 2 2 (-2) = true := rfl
  have hbit_true : ca 2 (-2) = false := by
    simpa using ca_even_pos 1 (by omega) (-2)
  have hcnt : aBoxClamp 3 = 3 := rfl
  refine ⟨⟨hbit_box, hbit_true⟩, ⟨hcnt, ?_⟩⟩
  rw [hcnt, a_three]
  omega

end Mathproofs.A266256
