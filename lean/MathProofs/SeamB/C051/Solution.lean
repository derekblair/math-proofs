import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Seam B Entry C051 (OEIS A266439): Colin Barker Rule 23 OFF-Cell Conjecture Bundle

Formalizes and proves Colin Barker's three-part conjecture bundle on `OEIS A266439`
(`%F` lines, Dec 30 2015 and Apr 15 2019; authored by Robert Price, Dec 29 2015)
against the frozen target contract `PIN-C051.md` v1
(`sha256: fd825f5739b30c7ff230c59988647d86bfe347b485ae3e84737788946f96438e`,
`delta_vs_source: NONE`), following the 1-step annihilation and formal-power-series
route in `SCOPING-C051.md` (§2.2, §5.1–§5.2):

1. **Wolfram Rule 23 truth table and structural symmetries (`rule23_truth_table`,
   `rule23_eq_neg_maj`, `rule23_symm`)**: proves the 8-case truth table by pure kernel
   reduction and identifies Rule 23 as the negated 3-input majority
   gate (`l + c + r ≤ 1`), which is left-right symmetric.
2. **Base value and 1-step defect annihilation (`ca_zero`, `a_zero`, `ca_one`)**:
   proves `a 0 = 0` and shows that generation `n = 1` is already spatially constant
   `true` across all of `ℤ` (`∀ j : ℤ, ca 1 j = true`), with no boundary defect.
3. **Spatially constant parity invariant (`ca_eq_decide_odd`)**: proves by induction on
   `n ≥ 1` that `ca n j = decide (Odd n)` across all `j : ℤ`, evolving globally on `ℤ`
   before restricting to `[-n, n]` inside `a n`.
4. **Window counts, closed form, and 4-step recurrence (`a_even_of_pos`, `a_odd`,
   `a_closed_form`, `a_recurrence`)**: deduces `a (2m) = 4m + 1` (`m ≥ 1`),
   `a (2m + 1) = 0` (`m ≥ 0`), Barker's rational closed form for `0 < n`, and the
   4-step linear recurrence `a n = 2 * a (n - 2) - a (n - 4)` for `4 < n`.
5. **Rational ordinary generating function and bundle (`a_gf`, `c051_a266439_bundle`,
   `a_gf_denom_isUnit`, `a_gf_unit_inv`)**: expands
   `((1 - X)^2 * (1 + X)^2) * F = F - 2 * (X^2 * F) + X^4 * F` in `PowerSeries ℚ`,
   proves equality with `X^2 * (5 - X^2)` coefficientwise via `PowerSeries.ext` and
   `PowerSeries.coeff_X_pow_mul'`, and confirms that the denominator is a unit in
   `PowerSeries ℚ`.
6. **Complementary ON-cell count, 8-rule equivalence class, causal-cone mirror,
   guard sharpness, and zero-padding trap (`a_add_aOn`, `caRule_eq_ca`,
   `caRule_equiv_class`, `a_dp_eq_a`, `a_spot_0_to_12`, `a_closed_form_false_zero`,
   `a_recurrence_false_four`, `aZeroPad_two_eq_three`)**.
-/

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

/-! ### Step 1: Rule 23 truth table and structural properties -/

theorem rule23_truth_table (l c r : Bool) :
    rule23 l c r =
      match l, c, r with
      | false, false, false => true
      | false, false, true  => true
      | false, true,  false => true
      | true,  false, false => true
      | _,     _,     _     => false := by
  cases l <;> cases c <;> cases r <;> rfl

/-- Rule 23 is the negated 3-input majority gate: it outputs `true` iff at most one
of `(l, c, r)` is `true`. -/
theorem rule23_eq_neg_maj (l c r : Bool) :
    rule23 l c r = decide (l.toNat + c.toNat + r.toNat ≤ 1) := by
  cases l <;> cases c <;> cases r <;> rfl

/-- Rule 23 is left-right reflection symmetric. -/
theorem rule23_symm (l c r : Bool) : rule23 l c r = rule23 r c l := by
  cases l <;> cases c <;> cases r <;> rfl

/-! ### Step 2: Base value `a 0 = 0` and 1-step annihilation on `ℤ` -/

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

/-- One-step defect annihilation on `ℤ`: at `n = 1`, every cell on `ℤ` is already `true`
because every neighborhood of the single-seed configuration contains at most one ON cell. -/
theorem ca_one (j : ℤ) : ca 1 j = true := by
  change rule23 (decide (j - 1 = 0)) (decide (j = 0)) (decide (j + 1 = 0)) = true
  have hsplit : j ≤ -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  rcases hsplit with h | rfl | rfl | rfl | h
  · rw [decide_eq_false (by omega : ¬(j - 1 = 0)),
        decide_eq_false (by omega : ¬(j = 0)),
        decide_eq_false (by omega : ¬(j + 1 = 0))]
    rfl
  · rw [decide_eq_false (by omega : ¬((-1 : ℤ) - 1 = 0)),
        decide_eq_false (by omega : ¬((-1 : ℤ) = 0)),
        decide_eq_true (by omega : (-1 : ℤ) + 1 = 0)]
    rfl
  · rw [decide_eq_false (by omega : ¬((0 : ℤ) - 1 = 0)),
        decide_eq_true (rfl : (0 : ℤ) = 0),
        decide_eq_false (by omega : ¬((0 : ℤ) + 1 = 0))]
    rfl
  · rw [decide_eq_true (by omega : (1 : ℤ) - 1 = 0),
        decide_eq_false (by omega : ¬((1 : ℤ) = 0)),
        decide_eq_false (by omega : ¬((1 : ℤ) + 1 = 0))]
    rfl
  · rw [decide_eq_false (by omega : ¬(j - 1 = 0)),
        decide_eq_false (by omega : ¬(j = 0)),
        decide_eq_false (by omega : ¬(j + 1 = 0))]
    rfl

/-! ### Step 3: Spatially constant global parity invariant for `n ≥ 1` -/

/-- For every generation `n ≥ 1`, `ca n` is spatially constant across all `j : ℤ` and
alternates globally with generation parity (`true` for odd `n`, `false` for even `n`). -/
theorem ca_eq_decide_odd : ∀ n : ℕ, 1 ≤ n → ∀ j : ℤ, ca n j = decide (Odd n) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction k with
  | zero =>
    intro j
    rw [Nat.zero_add, ca_one]
    have hodd1 : Odd 1 := ⟨0, rfl⟩
    rw [decide_eq_true hodd1]
  | succ k ih =>
    intro j
    have hstep : k + 1 + 1 = (k + 1) + 1 := by omega
    rw [hstep]
    change rule23 (ca (k + 1) (j - 1)) (ca (k + 1) j) (ca (k + 1) (j + 1)) =
      decide (Odd ((k + 1) + 1))
    rw [ih (j - 1), ih j, ih (j + 1)]
    rcases Nat.even_or_odd (k + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hnot : ¬ Odd (k + 1) := by
        rintro ⟨t, ht⟩
        omega
      have hodd : Odd ((k + 1) + 1) := ⟨m, by omega⟩
      rw [decide_eq_false hnot, decide_eq_true hodd]
      rfl
    · have hodd : Odd (k + 1) := ⟨m, hm⟩
      have hnot : ¬ Odd ((k + 1) + 1) := by
        rintro ⟨t, ht⟩
        omega
      rw [decide_eq_true hodd, decide_eq_false hnot]
      rfl

/-! ### Step 4: Window counting on `[-n, n]` and Barker's closed form (`0 < n`) -/

theorem a_even_of_pos {n : ℕ} (hn : 0 < n) (heven : ¬ Odd n) : a n = 2 * n + 1 := by
  unfold a
  have hfilter :
      (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca n j)) =
        Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    apply Finset.filter_true_of_mem
    intro j _
    rw [ca_eq_decide_odd n (by omega) j, decide_eq_false heven]
    rfl
  rw [hfilter, Int.card_Icc]
  omega

theorem a_odd {n : ℕ} (hodd : Odd n) : a n = 0 := by
  rcases hodd with ⟨m, rfl⟩
  unfold a
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _
  rw [ca_eq_decide_odd (2 * m + 1) (by omega) j, decide_eq_true ⟨m, rfl⟩]
  exact Bool.false_ne_true

theorem a_two_mul {m : ℕ} (hm : 1 ≤ m) : a (2 * m) = 4 * m + 1 := by
  have heven : ¬ Odd (2 * m) := by
    rintro ⟨t, ht⟩
    omega
  rw [a_even_of_pos (by omega) heven]
  omega

theorem a_two_mul_add_one (m : ℕ) : a (2 * m + 1) = 0 :=
  a_odd ⟨m, rfl⟩

theorem a_one : a 1 = 0 := a_two_mul_add_one 0
theorem a_two : a 2 = 5 := a_two_mul (m := 1) (by omega)
theorem a_three : a 3 = 0 := a_two_mul_add_one 1
theorem a_four : a 4 = 9 := a_two_mul (m := 2) (by omega)

theorem a_closed_form (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = (((-1 : ℚ) ^ n + 1) * (2 * (n : ℚ) + 1)) / 2 := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have heven : ¬ Odd (m + m) := by
      rintro ⟨t, ht⟩
      omega
    rw [a_even_of_pos hn heven]
    have hpow : (-1 : ℚ) ^ (m + m) = 1 := by
      rw [show m + m = 2 * m by omega, pow_mul]
      norm_num
    rw [hpow]
    push_cast
    ring
  · rw [a_odd ⟨m, rfl⟩]
    have hpow : (-1 : ℚ) ^ (2 * m + 1) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    rw [hpow]
    norm_num

/-! ### Step 5: Four-step linear recurrence (`4 < n`) -/

theorem a_recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have he0 : ¬ Odd (m + m) := by rintro ⟨t, ht⟩; omega
    have he2 : ¬ Odd (m + m - 2) := by rintro ⟨t, ht⟩; omega
    have he4 : ¬ Odd (m + m - 4) := by rintro ⟨t, ht⟩; omega
    rw [a_even_of_pos (by omega) he0,
        a_even_of_pos (by omega) he2,
        a_even_of_pos (by omega) he4]
    omega
  · have ho0 : Odd (2 * m + 1) := ⟨m, rfl⟩
    have ho2 : Odd (2 * m + 1 - 2) := ⟨m - 1, by omega⟩
    have ho4 : Odd (2 * m + 1 - 4) := ⟨m - 2, by omega⟩
    rw [a_odd ho0, a_odd ho2, a_odd ho4]
    norm_num

/-! ### Step 6: Rational ordinary generating function in `PowerSeries ℚ` and C051 bundle -/

theorem a_gf :
    ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
      (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2) *
      PowerSeries.mk (fun n => (a n : ℚ)) =
    (PowerSeries.X : PowerSeries ℚ) ^ 2 *
      (5 - (PowerSeries.X : PowerSeries ℚ) ^ 2) := by
  let X : PowerSeries ℚ := PowerSeries.X
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hlhs : ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) * F =
      F - 2 * (X ^ 2 * F) + X ^ 4 * F := by ring
  have hrhs : (X ^ 2 * (5 - X ^ 2) : PowerSeries ℚ) =
      5 * X ^ 2 - X ^ 4 := by ring
  change ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) * F =
      (X ^ 2 * (5 - X ^ 2) : PowerSeries ℚ)
  rw [hlhs, hrhs]
  apply PowerSeries.ext
  intro n
  dsimp only [X, F]
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
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
    have hne2 : k + 5 ≠ 2 := by omega
    have hne4 : k + 5 ≠ 4 := by omega
    simp only [h2, h4, hne2, hne4, ↓reduceIte,
      show k + 5 - 2 = k + 3 by omega, show k + 5 - 4 = k + 1 by omega]
    linarith

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
        (5 - (PowerSeries.X : PowerSeries ℚ) ^ 2)) :=
  ⟨a_zero, a_closed_form, a_recurrence, a_gf⟩

/-! ### Step 7: Unit invertibility, ON-cell complement, and 8-rule equivalence class -/

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
      ((PowerSeries.X : PowerSeries ℚ) ^ 2 *
        (5 - (PowerSeries.X : PowerSeries ℚ) ^ 2)) *
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
    _ = ((PowerSeries.X : PowerSeries ℚ) ^ 2 *
          (5 - (PowerSeries.X : PowerSeries ℚ) ^ 2)) *
        ((1 - (PowerSeries.X : PowerSeries ℚ)) ^ 2 *
          (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 2)⁻¹ := by
          rw [a_gf]

/-- Companion ON-cell count on `[-n, n]` (`OEIS A266437`). -/
def aOn (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j)).card

/-- Exact ON/OFF complement law on the active window `[-n, n]`: `a n + aOn n = 2n + 1`. -/
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

/-- Generic Wolfram ECA rule `code` update on `(l, c, r)`. -/
def ruleOf (code : ℕ) (l c r : Bool) : Bool :=
  Nat.testBit code (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Full-lattice single-seed evolution of Wolfram ECA `code` on `ℤ`. -/
def caRule (code : ℕ) : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => ruleOf code (caRule code n (j - 1)) (caRule code n j) (caRule code n (j + 1))

/-- Any Wolfram rule agreeing with Rule 23 on bits `{0, 1, 2, 4, 7}` has identical
single-seed evolution on all of `ℤ` because weight-2 neighborhoods `{3, 5, 6}` are never
encountered. -/
theorem caRule_eq_ca (code : ℕ)
    (h0 : Nat.testBit code 0 = true)
    (h1 : Nat.testBit code 1 = true)
    (h2 : Nat.testBit code 2 = true)
    (h4 : Nat.testBit code 4 = true)
    (h7 : Nat.testBit code 7 = false) :
    ∀ n : ℕ, ∀ j : ℤ, caRule code n j = ca n j := by
  intro n
  induction n with
  | zero =>
    intro j
    rfl
  | succ n ih =>
    intro j
    rcases n with _ | m
    · change ruleOf code (decide (j - 1 = 0)) (decide (j = 0)) (decide (j + 1 = 0)) = ca 1 j
      rw [ca_one]
      have hsplit : j ≤ -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
      rcases hsplit with h | rfl | rfl | rfl | h
      · rw [decide_eq_false (by omega : ¬(j - 1 = 0)),
            decide_eq_false (by omega : ¬(j = 0)),
            decide_eq_false (by omega : ¬(j + 1 = 0))]
        simpa [ruleOf] using h0
      · rw [decide_eq_false (by omega : ¬((-1 : ℤ) - 1 = 0)),
            decide_eq_false (by omega : ¬((-1 : ℤ) = 0)),
            decide_eq_true (by omega : (-1 : ℤ) + 1 = 0)]
        simpa [ruleOf] using h1
      · rw [decide_eq_false (by omega : ¬((0 : ℤ) - 1 = 0)),
            decide_eq_true (rfl : (0 : ℤ) = 0),
            decide_eq_false (by omega : ¬((0 : ℤ) + 1 = 0))]
        simpa [ruleOf] using h2
      · rw [decide_eq_true (by omega : (1 : ℤ) - 1 = 0),
            decide_eq_false (by omega : ¬((1 : ℤ) = 0)),
            decide_eq_false (by omega : ¬((1 : ℤ) + 1 = 0))]
        simpa [ruleOf] using h4
      · rw [decide_eq_false (by omega : ¬(j - 1 = 0)),
            decide_eq_false (by omega : ¬(j = 0)),
            decide_eq_false (by omega : ¬(j + 1 = 0))]
        simpa [ruleOf] using h0
    · change ruleOf code (caRule code (m + 1) (j - 1)) (caRule code (m + 1) j)
          (caRule code (m + 1) (j + 1)) =
        rule23 (ca (m + 1) (j - 1)) (ca (m + 1) j) (ca (m + 1) (j + 1))
      rw [ih (j - 1), ih j, ih (j + 1)]
      rw [ca_eq_decide_odd (m + 1) (by omega) (j - 1),
          ca_eq_decide_odd (m + 1) (by omega) j,
          ca_eq_decide_odd (m + 1) (by omega) (j + 1)]
      cases decide (Odd (m + 1))
      · have hr : rule23 false false false = true := rfl
        rw [hr]
        simpa [ruleOf] using h0
      · have hr : rule23 true true true = false := rfl
        rw [hr]
        simpa [ruleOf] using h7

/-- The 8-rule single-seed equivalence class noted on `OEIS A266434`:
Rules `23, 31, 55, 63, 87, 95, 119, 127` produce the exact same space-time diagram on `ℤ`. -/
theorem caRule_equiv_class (code : ℕ)
    (hcode : code ∈ ([23, 31, 55, 63, 87, 95, 119, 127] : List ℕ)) :
    ∀ n : ℕ, ∀ j : ℤ, caRule code n j = ca n j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
  rcases hcode with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact caRule_eq_ca _ rfl rfl rfl rfl rfl

/-! ### Step 8: Non-vacuity — causal-cone mirror, OEIS spot checks, sharpness, zero-padding trap -/

/-- One causal-cone contraction step on a list of adjacent spatial states. -/
def coneStep : List Bool → List Bool
  | l :: c :: r :: rest => rule23 l c r :: coneStep (c :: r :: rest)
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
    change rule23 (ca m s) (ca m (s + 1)) (ca m (s + 1 + 1)) =
      rule23 (ca m ((s + 1) - 1)) (ca m (s + 1)) (ca m ((s + 1) + 1))
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

/-- Pure kernel `rfl` check of `a_dp` against OEIS `A266439` for `n = 0..12`. -/
theorem a_dp_spot_0_to_12 :
    (List.range 13).map a_dp = [0, 0, 5, 0, 9, 0, 13, 0, 17, 0, 21, 0, 25] :=
  rfl

/-- Kernel-checked agreement of the pinned `a` with OEIS `A266439` for `n = 0..12`. -/
theorem a_spot_0_to_12 :
    (List.range 13).map a = [0, 0, 5, 0, 9, 0, 13, 0, 17, 0, 21, 0, 25] := by
  have hfun : a = a_dp := funext (fun n => (a_dp_eq_a n).symm)
  rw [hfun]
  exact a_dp_spot_0_to_12

/-- Sharpness of `0 < n` in `a_closed_form`: fails at `n = 0` (`0 ≠ 1`). -/
theorem a_closed_form_false_zero :
    (a 0 : ℚ) ≠ (((-1 : ℚ) ^ 0 + 1) * (2 * (0 : ℚ) + 1)) / 2 := by
  norm_num [a_zero]

/-- Sharpness of `4 < n` in `a_recurrence`: fails at `n = 4` (`9 ≠ 10`). -/
theorem a_recurrence_false_four :
    (a 4 : ℤ) ≠ 2 * (a (4 - 2) : ℤ) - (a (4 - 4) : ℤ) := by
  norm_num [a_four, a_two, a_zero]

/-- Growing-window zero-padded evolution (the erroneous convention noted in `PIN-C051.md`
fidelity note 2, where cells outside `[-m, m]` at step `m` are forced to `false`). -/
def caZeroPad : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | m + 1, j =>
    let get (k : ℤ) : Bool := if -(m : ℤ) ≤ k ∧ k ≤ (m : ℤ) then caZeroPad m k else false
    if -((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + 1 : ℕ) : ℤ) then
      rule23 (get (j - 1)) (get j) (get (j + 1))
    else
      false

/-- OFF-cell count on `[-n, n]` under the erroneous growing-window zero-padded convention. -/
def aZeroPad (n : ℕ) : ℕ :=
  ((List.range (2 * n + 1)).filter (fun i => !(caZeroPad n ((i : ℤ) - (n : ℤ))))).length

/-- Kernel `rfl` confirmation of the zero-padding trap (`PIN-C051.md` fidelity note 2):
growing-window zero-padding gives `10001` (`3` OFF cells) at `n = 2`, whereas true
`ℤ`-evolution gives `00000` (`a 2 = 5`). -/
theorem aZeroPad_two_eq_three : aZeroPad 2 = 3 ∧ aZeroPad 2 ≠ a 2 := by
  have h : aZeroPad 2 = 3 := rfl
  refine ⟨h, ?_⟩
  rw [h, a_two]
  omega

end Mathproofs.A266439Rule23Off
