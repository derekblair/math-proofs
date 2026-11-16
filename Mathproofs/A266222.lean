import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Seam B Entry C050 (OEIS A266222): Colin Barker Rule 7 OFF-Cell Conjecture Bundle

Formalizes and proves Colin Barker's three-part conjecture bundle on `OEIS A266222`
(`%F` lines 16–20, Dec 26 2015 and Apr 13 2019; authored by Robert Price, Dec 24 2015)
against the frozen target contract `PIN-C050.md` v1 (`delta_vs_source: NONE`), following
the 2-step defect-annihilation and formal-power-series route in `SCOPING-C050.md` (§2.2, §5.2):

1. **Wolfram Rule 7 bitmask equivalence (`rule7_eq_testBit`)**: verifies the Boolean rule
   `(!l && !c) || (!l && c && !r)` matches bit `4*l + 2*c + r` of `7 = 0b00000111`.
2. **Initial generations and 2-step defect annihilation (`ca_zero`, `a_zero`, `ca_one`,
   `a_one`, `ca_two`)**: proves `ca 1 j = decide (j ≠ 1)` on all of `ℤ` (a single OFF defect
   at `j = 1` against an ON background) and `ca 2 j = false` for all `j : ℤ`.
3. **Spatially constant parity invariant (`ca_eq_decide_odd`)**: proves by induction on `n ≥ 2`
   that `ca n j = decide (Odd n)` across all `j : ℤ`, with zero boundary case splits because
   `ca` is evolved globally on `ℤ` before restricting to `[-n, n]` inside `a n`.
4. **Window counts, closed form, and 4-step recurrence (`a_even_of_ge_two`, `a_odd_of_ge_two`,
   `a_closed_form`, `a_recurrence`)**: deduces `a (2m) = 4m + 1` and `a (2m + 1) = 0` for `m ≥ 1`,
   the closed form for `n > 1`, and the recurrence `a n = 2 * a (n - 2) - a (n - 4)` for `n > 5`.
5. **Rational ordinary generating function (`a_gf`, `c050_bundle`)**: expands
   `((1 - X)^2 * (1 + X)^2) * F = F - 2 * (X^2 * F) + X^4 * F` in `PowerSeries ℚ` and verifies
   equality with `X * (1 + 5*X - 2*X^2 - X^3 + X^4)` coefficient-by-coefficient via
   `PowerSeries.ext` and `PowerSeries.coeff_X_pow_mul'`.
6. **Computable causal-cone mirror, guard sharpness, and zero-padding trap (`a_dp`, `a_dp_eq_a`,
   `a_spot_0_to_12`, `aZeroPad_two_eq_three`)**: provides a polynomial-time list mirror formally
   proved equal to `a` on all `n : ℕ` for kernel `rfl` OEIS spot checks (`n = 0..12`), proves
   sharpness at `n = 0, 1` and `n = 4, 5`, and formalizes why naive growing-window zero-padding
   yields `3` instead of `a 2 = 5`.
-/

namespace A266222

def rule7 (l c r : Bool) : Bool := (!l && !c) || (!l && c && !r)

def ca : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule7 (ca n (j - 1)) (ca n j) (ca n (j + 1))

def a (n : ℕ) : ℕ := ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca n j))).card

/-! ### Step 0: Wolfram ECA Rule 7 bit-index agreement -/

/-- `rule7 l c r` agrees on all 8 neighborhood triples with Wolfram ECA Rule `7 = 0b00000111`
at index `4 * l.toNat + 2 * c.toNat + r.toNat`. -/
theorem rule7_eq_testBit (l c r : Bool) :
    rule7 l c r = Nat.testBit 7 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;> rfl

/-- Structural property of Rule 7: whenever at least two of `(l, c, r)` are `true`,
`rule7 l c r = false` (equivalently, `rule7 l c r = true` requires at least two `false` inputs). -/
theorem rule7_eq_false_of_two_true {l c r : Bool}
    (h : (l = true ∧ c = true) ∨ (l = true ∧ r = true) ∨ (c = true ∧ r = true)) :
    rule7 l c r = false := by
  cases l <;> cases c <;> cases r <;> simp_all [rule7]

/-! ### Steps 1–3: Generations `n = 0, 1, 2` and 2-step defect annihilation on `ℤ` -/

theorem ca_zero (j : ℤ) : ca 0 j = decide (j = 0) :=
  rfl

theorem a_zero : a 0 = 0 := by
  unfold a
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  rw [Finset.mem_Icc] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  simp [ca]

/-- Generation `1` global profile on `ℤ`: every integer is ON (`true`) except the single
OFF (`false`) defect at `j = 1`. -/
theorem ca_one (j : ℤ) : ca 1 j = decide (j ≠ 1) := by
  change rule7 (decide (j - 1 = 0)) (decide (j = 0)) (decide (j + 1 = 0)) = decide (j ≠ 1)
  have hsplit : j ≤ -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  rcases hsplit with h | rfl | rfl | rfl | h
  · rw [decide_eq_false (by omega : ¬(j - 1 = 0)),
        decide_eq_false (by omega : ¬(j = 0)),
        decide_eq_false (by omega : ¬(j + 1 = 0)),
        decide_eq_true (by omega : j ≠ 1)]
    rfl
  · rw [decide_eq_false (by omega : ¬((-1 : ℤ) - 1 = 0)),
        decide_eq_false (by omega : ¬((-1 : ℤ) = 0)),
        decide_eq_true (by omega : (-1 : ℤ) + 1 = 0),
        decide_eq_true (by omega : (-1 : ℤ) ≠ 1)]
    rfl
  · rw [decide_eq_false (by omega : ¬((0 : ℤ) - 1 = 0)),
        decide_eq_true (rfl : (0 : ℤ) = 0),
        decide_eq_false (by omega : ¬((0 : ℤ) + 1 = 0)),
        decide_eq_true (by omega : (0 : ℤ) ≠ 1)]
    rfl
  · rw [decide_eq_true (by omega : (1 : ℤ) - 1 = 0),
        decide_eq_false (by omega : ¬((1 : ℤ) = 0)),
        decide_eq_false (by omega : ¬((1 : ℤ) + 1 = 0)),
        decide_eq_false (by omega : ¬((1 : ℤ) ≠ 1))]
    rfl
  · rw [decide_eq_false (by omega : ¬(j - 1 = 0)),
        decide_eq_false (by omega : ¬(j = 0)),
        decide_eq_false (by omega : ¬(j + 1 = 0)),
        decide_eq_true (by omega : j ≠ 1)]
    rfl

theorem a_one : a 1 = 1 := by
  unfold a
  rw [Finset.card_eq_one]
  refine ⟨1, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, ca_one]
  constructor
  · rintro ⟨⟨_, _⟩, hj⟩
    by_contra hne
    rw [decide_eq_true hne] at hj
    exact Bool.false_ne_true hj
  · rintro rfl
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [decide_eq_false (by omega : ¬((1 : ℤ) ≠ 1))]
    rfl

/-- Two-step defect annihilation on `ℤ`: at `n = 2`, the unique `n = 1` defect at `j = 1`
is annihilated and every cell on `ℤ` becomes `false`. -/
theorem ca_two (j : ℤ) : ca 2 j = false := by
  change rule7 (ca 1 (j - 1)) (ca 1 j) (ca 1 (j + 1)) = false
  rw [ca_one, ca_one, ca_one]
  have hsplit : j ≤ -1 ∨ j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j := by omega
  rcases hsplit with h | rfl | rfl | rfl | h
  · rw [decide_eq_true (by omega : j - 1 ≠ 1),
        decide_eq_true (by omega : j ≠ 1),
        decide_eq_true (by omega : j + 1 ≠ 1)]
    rfl
  · rw [decide_eq_true (by omega : (0 : ℤ) - 1 ≠ 1),
        decide_eq_true (by omega : (0 : ℤ) ≠ 1),
        decide_eq_false (by omega : ¬((0 : ℤ) + 1 ≠ 1))]
    rfl
  · rw [decide_eq_true (by omega : (1 : ℤ) - 1 ≠ 1),
        decide_eq_false (by omega : ¬((1 : ℤ) ≠ 1)),
        decide_eq_true (by omega : (1 : ℤ) + 1 ≠ 1)]
    rfl
  · rw [decide_eq_false (by omega : ¬((2 : ℤ) - 1 ≠ 1)),
        decide_eq_true (by omega : (2 : ℤ) ≠ 1),
        decide_eq_true (by omega : (2 : ℤ) + 1 ≠ 1)]
    rfl
  · rw [decide_eq_true (by omega : j - 1 ≠ 1),
        decide_eq_true (by omega : j ≠ 1),
        decide_eq_true (by omega : j + 1 ≠ 1)]
    rfl

/-! ### Step 4: Spatially constant parity invariant for `n ≥ 2` -/

/-- For every generation `n ≥ 2`, `ca n` is spatially constant across all `j : ℤ` and
alternates globally with generation parity (`false` for even `n`, `true` for odd `n`). -/
theorem ca_eq_decide_odd : ∀ n : ℕ, 2 ≤ n → ∀ j : ℤ, ca n j = decide (Odd n) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  clear hn
  induction k with
  | zero =>
    intro j
    rw [Nat.zero_add, ca_two]
    have hnot : ¬ Odd 2 := by
      rintro ⟨m, hm⟩
      omega
    rw [decide_eq_false hnot]
  | succ k ih =>
    intro j
    have hstep : k + 1 + 2 = (k + 2) + 1 := by omega
    rw [hstep]
    change rule7 (ca (k + 2) (j - 1)) (ca (k + 2) j) (ca (k + 2) (j + 1)) =
      decide (Odd ((k + 2) + 1))
    rw [ih (j - 1), ih j, ih (j + 1)]
    rcases Nat.even_or_odd (k + 2) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hnot : ¬ Odd (k + 2) := by
        rintro ⟨t, ht⟩
        omega
      have hodd : Odd ((k + 2) + 1) := ⟨m, by omega⟩
      rw [decide_eq_false hnot, decide_eq_true hodd]
      rfl
    · have hodd : Odd (k + 2) := ⟨m, hm⟩
      have hnot : ¬ Odd ((k + 2) + 1) := by
        rintro ⟨t, ht⟩
        omega
      rw [decide_eq_true hodd, decide_eq_false hnot]
      rfl

/-! ### Step 5: Window counting on `[-n, n]` and closed form (`n > 1`) -/

theorem a_even_of_ge_two {n : ℕ} (hn : 2 ≤ n) (heven : ¬ Odd n) : a n = 2 * n + 1 := by
  unfold a
  have hfilter :
      (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca n j)) =
        Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    apply Finset.filter_true_of_mem
    intro j _
    rw [ca_eq_decide_odd n hn j, decide_eq_false heven]
    rfl
  rw [hfilter, Int.card_Icc]
  omega

theorem a_odd_of_ge_two {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n) : a n = 0 := by
  unfold a
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _
  rw [ca_eq_decide_odd n hn j, decide_eq_true hodd]
  exact Bool.false_ne_true

theorem a_two_mul {m : ℕ} (hm : 1 ≤ m) : a (2 * m) = 4 * m + 1 := by
  have hn : 2 ≤ 2 * m := by omega
  have heven : ¬ Odd (2 * m) := by
    rintro ⟨t, ht⟩
    omega
  rw [a_even_of_ge_two hn heven]
  omega

theorem a_two_mul_add_one {m : ℕ} (hm : 1 ≤ m) : a (2 * m + 1) = 0 := by
  exact a_odd_of_ge_two (by omega) ⟨m, rfl⟩

theorem a_two : a 2 = 5 := a_two_mul (m := 1) (by omega)
theorem a_three : a 3 = 0 := a_two_mul_add_one (m := 1) (by omega)
theorem a_four : a 4 = 9 := a_two_mul (m := 2) (by omega)
theorem a_five : a 5 = 0 := a_two_mul_add_one (m := 2) (by omega)

theorem a_closed_form : ∀ n : ℕ, n > 1 → (a n : ℤ) * 2 = (1 + (-1 : ℤ) ^ n) * (1 + 2 * (n : ℤ)) := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hn2 : 2 ≤ m + m := by omega
    have heven : ¬ Odd (m + m) := by
      rintro ⟨t, ht⟩
      omega
    rw [a_even_of_ge_two hn2 heven]
    have hpow : (-1 : ℤ) ^ (m + m) = 1 := by
      rw [show m + m = 2 * m by omega, pow_mul]
      norm_num
    rw [hpow]
    push_cast
    ring
  · have hn2 : 2 ≤ 2 * m + 1 := by omega
    rw [a_odd_of_ge_two hn2 ⟨m, rfl⟩]
    have hpow : (-1 : ℤ) ^ (2 * m + 1) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    rw [hpow]
    norm_num

/-! ### Step 6: Four-step linear recurrence (`n > 5`) -/

theorem a_recurrence : ∀ n : ℕ, n > 5 → (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  intro n hn
  have h0 := a_closed_form n (by omega)
  have h2 := a_closed_form (n - 2) (by omega)
  have h4 := a_closed_form (n - 4) (by omega)
  have hp0 : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n - 4) := by
    rw [show n = (n - 4) + 4 by omega, pow_add]
    norm_num
  have hp2 : (-1 : ℤ) ^ (n - 2) = (-1 : ℤ) ^ (n - 4) := by
    rw [show n - 2 = (n - 4) + 2 by omega, pow_add]
    norm_num
  rw [hp0] at h0
  rw [hp2] at h2
  have hc2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hc4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
  rw [hc2] at h2
  rw [hc4] at h4
  have htwice : ((a n : ℤ) - (2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ))) * 2 = 0 := by
    calc
      ((a n : ℤ) - (2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ))) * 2
          = (a n : ℤ) * 2 - 2 * ((a (n - 2) : ℤ) * 2) + (a (n - 4) : ℤ) * 2 := by ring
      _ = (1 + (-1 : ℤ) ^ (n - 4)) * (1 + 2 * (n : ℤ))
          - 2 * ((1 + (-1 : ℤ) ^ (n - 4)) * (1 + 2 * ((n : ℤ) - 2)))
          + (1 + (-1 : ℤ) ^ (n - 4)) * (1 + 2 * ((n : ℤ) - 4)) := by rw [h0, h2, h4]
      _ = 0 := by ring
  omega

/-! ### Step 7: Rational ordinary generating function in `PowerSeries ℚ` and full C050 bundle -/

theorem a_gf : (((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ) * PowerSeries.mk (fun n => (a n : ℚ))) = (PowerSeries.X * (1 + 5 * PowerSeries.X - 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 4) : PowerSeries ℚ) := by
  let X : PowerSeries ℚ := PowerSeries.X
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hlhs : ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) * F =
      F - 2 * (X ^ 2 * F) + X ^ 4 * F := by ring
  have hrhs : (X * (1 + 5 * X - 2 * X ^ 2 - X ^ 3 + X ^ 4) : PowerSeries ℚ) =
      X + 5 * X ^ 2 - 2 * X ^ 3 - X ^ 4 + X ^ 5 := by ring
  change ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) * F =
      (X * (1 + 5 * X - 2 * X ^ 2 - X ^ 3 + X ^ 4) : PowerSeries ℚ)
  rw [hlhs, hrhs]
  apply PowerSeries.ext
  intro n
  dsimp only [X, F]
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  rcases n with _ | _ | _ | _ | _ | _ | k
  · norm_num [a_zero]
  · norm_num [a_zero, a_one]
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
    have hne3 : k + 6 ≠ 3 := by omega
    have hne4 : k + 6 ≠ 4 := by omega
    have hne5 : k + 6 ≠ 5 := by omega
    simp only [h2, h4, hne1, hne2, hne3, hne4, hne5, ↓reduceIte,
      show k + 6 - 2 = k + 4 by omega, show k + 6 - 4 = k + 2 by omega]
    linarith

theorem c050_bundle : (∀ n : ℕ, n > 1 → (a n : ℤ) * 2 = (1 + (-1 : ℤ) ^ n) * (1 + 2 * (n : ℤ))) ∧ (∀ n : ℕ, n > 5 → (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧ ((((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ) * PowerSeries.mk (fun n => (a n : ℚ))) = (PowerSeries.X * (1 + 5 * PowerSeries.X - 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 4) : PowerSeries ℚ)) :=
  ⟨a_closed_form, a_recurrence, a_gf⟩

/-! ### Non-vacuity: Computable causal-cone mirror, OEIS spot checks, and guard sharpness -/

/-- One causal-cone contraction step on a list of adjacent spatial states. -/
def coneStep : List Bool → List Bool
  | l :: c :: r :: rest => rule7 l c r :: coneStep (c :: r :: rest)
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
    change rule7 (ca m s) (ca m (s + 1)) (ca m (s + 1 + 1)) =
      rule7 (ca m ((s + 1) - 1)) (ca m (s + 1)) (ca m ((s + 1) + 1))
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
    have hnotmem : s ∉ (Finset.Icc (s + 1) ((s + 1) + (len : ℤ) - 1)).filter (fun j => !(ca m j)) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hins, Finset.filter_insert]
    simp only [caRow, List.filter]
    cases hca : ca m s
    · simp only [Bool.not_false, ↓reduceIte, List.length_cons,
        Finset.card_insert_of_notMem hnotmem, filter_caRow_length m len (s + 1)]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        filter_caRow_length m len (s + 1)]

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

/-- Pure kernel `rfl` check of `a_dp` against OEIS `A266222` for `n = 0..12`. -/
theorem a_dp_spot_0_to_12 :
    (List.range 13).map a_dp = [0, 1, 5, 0, 9, 0, 13, 0, 17, 0, 21, 0, 25] :=
  rfl

/-- Kernel-checked agreement of the pinned `A266222.a` with OEIS `A266222` for `n = 0..12`. -/
theorem a_spot_0_to_12 :
    (List.range 13).map a = [0, 1, 5, 0, 9, 0, 13, 0, 17, 0, 21, 0, 25] := by
  have hfun : a = a_dp := funext (fun n => (a_dp_eq_a n).symm)
  rw [hfun]
  exact a_dp_spot_0_to_12

/-- Sharpness of `n > 1` in `a_closed_form`: fails at `n = 0` (`0 ≠ 2`). -/
theorem a_closed_form_false_zero :
    (a 0 : ℤ) * 2 ≠ (1 + (-1 : ℤ) ^ 0) * (1 + 2 * (0 : ℤ)) := by
  norm_num [a_zero]

/-- Sharpness of `n > 1` in `a_closed_form`: fails at `n = 1` (`2 ≠ 0`). -/
theorem a_closed_form_false_one :
    (a 1 : ℤ) * 2 ≠ (1 + (-1 : ℤ) ^ 1) * (1 + 2 * (1 : ℤ)) := by
  norm_num [a_one]

/-- Sharpness of `n > 5` in `a_recurrence`: fails at `n = 4` (`9 ≠ 10`). -/
theorem a_recurrence_false_four :
    (a 4 : ℤ) ≠ 2 * (a 2 : ℤ) - (a 0 : ℤ) := by
  norm_num [a_four, a_two, a_zero]

/-- Sharpness of `n > 5` in `a_recurrence`: fails at `n = 5` (`0 ≠ -1`). -/
theorem a_recurrence_false_five :
    (a 5 : ℤ) ≠ 2 * (a 3 : ℤ) - (a 1 : ℤ) := by
  norm_num [a_five, a_three, a_one]

/-- Growing-window zero-padded evolution (the erroneous convention noted in `PIN-C050.md`
fidelity note 2, where cells outside `[-m, m]` at step `m` are forced to `false`). -/
def caZeroPad : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | m + 1, j =>
    let get (k : ℤ) : Bool := if -(m : ℤ) ≤ k ∧ k ≤ (m : ℤ) then caZeroPad m k else false
    if -((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + 1 : ℕ) : ℤ) then
      rule7 (get (j - 1)) (get j) (get (j + 1))
    else
      false

/-- OFF-cell count on `[-n, n]` under the erroneous growing-window zero-padded convention. -/
def aZeroPad (n : ℕ) : ℕ :=
  ((List.range (2 * n + 1)).filter (fun i => !(caZeroPad n ((i : ℤ) - (n : ℤ))))).length

/-- Kernel `rfl` confirmation of the zero-padding trap (`PIN-C050.md` fidelity note 2):
growing-window zero-padding gives `3` at `n = 2`, whereas true `ℤ`-evolution gives `a 2 = 5`. -/
theorem aZeroPad_two_eq_three : aZeroPad 2 = 3 ∧ aZeroPad 2 ≠ a 2 := by
  have h : aZeroPad 2 = 3 := rfl
  refine ⟨h, ?_⟩
  rw [h, a_two]
  omega

end A266222
