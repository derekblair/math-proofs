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
# Seam B Entry C057 (OEIS A266437): Rule 23 ON-Cell Count Conjecture Bundle

Formalizes and proves Colin Barker's closed-form and 4-step recurrence conjectures
(Dec 30 2015 and Apr 15 2019) together with Michael De Vlieger's empirical rational
ordinary generating function (Dec 29 2015) and the initial value `a 0 = 1` for
`OEIS A266437` (authored by Robert Price, Dec 29 2015), against the frozen target
contract `PIN-C057.md` v1 (`sha256: fd1ba2551dcd430f6745e899ae570414a2f12060f958a0b5ae1dc2d7c8bd8378`,
`Statement.lean sha256: 8c24bbd7f3d1921f9485c189ddca7996b91ef50084e956c503712746802ff1b4`,
`delta_vs_source: NONE`), following the one-step global uniformity and formal power
series route in `SCOPING-C057.md` (§2.1, §5.1–§5.2):

1. **Wolfram Rule 23 characterization (`rule23_eq_testBit`, `rule23_eq_at_most_one_true`,
   `rule23_symm`, `rule23_const`)**: verifies the 4-minterm DNF matches bit `4*l + 2*c + r`
   of `23 = 0b00010111`, outputs `true` iff at most one input is `true` (negated 3-input
   majority), is amphichiral (`rule23 l c r = rule23 r c l`), and satisfies `rule23 b b b = !b`.
2. **Initial value and 1-step global uniformity (`ca_zero`, `a_zero`, `ca_one`,
   `ca_eq_decide_odd`)**: proves `a 0 = 1`, `ca 1 j = true` across all `j : ℤ` (unlike Rule 7,
   Rule 23 reaches global spatial uniformity already at generation `n = 1`), and by induction
   `ca n j = decide (Odd n)` for every `n ≥ 1` and every `j : ℤ`.
3. **Window counts, closed form, and 4-step recurrence (`a_odd`, `a_even_of_pos`,
   `a_two_mul_add_one`, `a_two_mul`, `a_closed_form`, `a_recurrence`)**: establishes
   `a (2m + 1) = 4m + 3` for all `m ≥ 0`, `a (2m) = 0` for all `m ≥ 1`, Barker's cleared
   closed form for `n > 0`, and Barker's exact `ℤ` 4-step recurrence for `n > 4`.
4. **Rational ordinary generating function (`a_gf`, `a_gf_denom_eq_devlieger`,
   `a_gf_denom_isUnit`, `a_gf_unit_inv`, `c057_a266437_bundle`)**: expands
   `((1 - X)^2 * (1 + X)^2) * F = F - 2 * (X^2 * F) + X^4 * F` in `PowerSeries ℚ`,
   checks all coefficients via `PowerSeries.ext` and `PowerSeries.coeff_X_pow_mul'`,
   verifies De Vlieger's `(-1 + X^2)^2` denominator equality and unit invertibility,
   and bundles all four pinned theorems in `c057_a266437_bundle`.
5. **Complement law, 8-rule equivalence class, causal-cone mirror, guard sharpness, and
   zero-padding trap (`a_add_off`, `caRule_eq_ca`, `caRule_equiv_class`, `a_dp`, `a_dp_eq_a`,
   `a_spot_0_to_12`, `a_closed_form_false_zero`, `a_recurrence_false_four`,
   `aZeroPad_two_eq_two`)**: proves `a n + aOff n = 2 * n + 1`, shows all eight rules
   `{23, 31, 55, 63, 87, 95, 119, 127}` yield identical spacetime lattices from the single-ON
   seed because weight-2 neighborhoods never occur, proves an $O(n^2)$ computable causal-cone
   mirror equal to `a` for pure kernel `rfl` OEIS spot checks (`n = 0..12`), proves exact
   sharpness of `n > 0` and `n > 4`, and formalizes the growing-window zero-padding failure
   at `n = 2` (`2 ≠ 0`).
-/

namespace A266437

def rule23 (l c r : Bool) : Bool :=
  (!l && !c && !r) || (!l && !c && r) || (!l && c && !r) || (l && !c && !r)

def ca : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule23 (ca n (j - 1)) (ca n j) (ca n (j + 1))

def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j = true)).card

/-! ### Step 0: Wolfram ECA Rule 23 bitmask and structural properties -/

/-- `rule23 l c r` agrees on all 8 neighborhood triples with Wolfram ECA Rule `23 = 0b00010111`
at bit index `4 * l.toNat + 2 * c.toNat + r.toNat`. -/
theorem rule23_eq_testBit (l c r : Bool) :
    rule23 l c r = Nat.testBit 23 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;> rfl

/-- Negated 3-input majority characterization: `rule23 l c r = true` iff at most one of
`l, c, r` is `true`. -/
theorem rule23_eq_at_most_one_true (l c r : Bool) :
    rule23 l c r = decide (l.toNat + c.toNat + r.toNat ≤ 1) := by
  cases l <;> cases c <;> cases r <;> rfl

/-- Amphichiral (left-right reflection) symmetry of Rule 23. -/
theorem rule23_symm (l c r : Bool) : rule23 l c r = rule23 r c l := by
  cases l <;> cases c <;> cases r <;> rfl

/-- Constant-neighborhood flip: on any spatially uniform state `b`, Rule 23 outputs `!b`. -/
theorem rule23_const (b : Bool) : rule23 b b b = !b := by
  cases b <;> rfl

/-! ### Steps 1–2: Base value `a 0 = 1` and 1-step global uniformity on `ℤ` -/

theorem ca_zero (j : ℤ) : ca 0 j = decide (j = 0) :=
  rfl

theorem a_zero : a 0 = 1 := by
  unfold a
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  rw [ca_zero]
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩
    omega
  · rintro rfl
    exact ⟨⟨by omega, by omega⟩, rfl⟩

/-- One-step global uniformity on `ℤ`: because `ca 0` has only a single `true` cell at `j = 0`,
every 3-cell neighborhood `(j - 1, j, j + 1)` contains at most one `true` cell, so `ca 1 j = true`
for every `j : ℤ`. -/
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

/-- Spatially constant parity invariant for all `n ≥ 1`: every cell on `ℤ` equals
`decide (Odd n)`, alternating globally between all-ON (`true`, odd `n`) and all-OFF
(`false`, positive even `n`). -/
theorem ca_eq_decide_odd : ∀ n : ℕ, 1 ≤ n → ∀ j : ℤ, ca n j = decide (Odd n) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction k with
  | zero =>
    intro j
    rw [Nat.zero_add, ca_one]
    have hodd : Odd 1 := ⟨0, rfl⟩
    rw [decide_eq_true hodd]
  | succ k ih =>
    intro j
    have hstep : k + 1 + 1 = (k + 1) + 1 := rfl
    rw [hstep]
    change rule23 (ca (k + 1) (j - 1)) (ca (k + 1) j) (ca (k + 1) (j + 1)) =
      decide (Odd ((k + 1) + 1))
    rw [ih (j - 1), ih j, ih (j + 1), rule23_const]
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

/-! ### Step 3: Window counting on `[-n, n]` and closed form (`n > 0`) -/

theorem a_odd {n : ℕ} (hodd : Odd n) : a n = 2 * n + 1 := by
  have hn : 1 ≤ n := by
    rcases hodd with ⟨m, rfl⟩
    omega
  unfold a
  have hfilter :
      (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ca n j = true) =
        Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    apply Finset.filter_true_of_mem
    intro j _
    rw [ca_eq_decide_odd n hn j, decide_eq_true hodd]
  rw [hfilter, Int.card_Icc]
  omega

theorem a_even_of_pos {n : ℕ} (hn : 1 ≤ n) (heven : ¬ Odd n) : a n = 0 := by
  unfold a
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _
  rw [ca_eq_decide_odd n hn j, decide_eq_false heven]
  exact Bool.false_ne_true

theorem a_two_mul_add_one (m : ℕ) : a (2 * m + 1) = 4 * m + 3 := by
  rw [a_odd ⟨m, rfl⟩]
  omega

theorem a_two_mul {m : ℕ} (hm : 1 ≤ m) : a (2 * m) = 0 := by
  have hn : 1 ≤ 2 * m := by omega
  have heven : ¬ Odd (2 * m) := by
    rintro ⟨t, ht⟩
    omega
  exact a_even_of_pos hn heven

theorem a_one : a 1 = 3 := a_two_mul_add_one 0
theorem a_two : a 2 = 0 := a_two_mul (m := 1) (by omega)
theorem a_three : a 3 = 7 := a_two_mul_add_one 1
theorem a_four : a 4 = 0 := a_two_mul (m := 2) (by omega)

theorem a_closed_form (n : ℕ) (hn : n > 0) :
    (a n : ℤ) * 2 = (1 - (-1 : ℤ) ^ n) * (2 * (n : ℤ) + 1) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hn1 : 1 ≤ m + m := by omega
    have heven : ¬ Odd (m + m) := by
      rintro ⟨t, ht⟩
      omega
    rw [a_even_of_pos hn1 heven]
    have hpow : (-1 : ℤ) ^ (m + m) = 1 := by
      rw [show m + m = 2 * m by omega, pow_mul]
      norm_num
    rw [hpow]
    norm_num
  · rw [a_odd ⟨m, rfl⟩]
    have hpow : (-1 : ℤ) ^ (2 * m + 1) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    rw [hpow]
    push_cast
    ring

/-! ### Step 4: Four-step linear recurrence (`n > 4`) -/

theorem a_recurrence (n : ℕ) (hn : n > 4) :
    (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
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
      _ = (1 - (-1 : ℤ) ^ (n - 4)) * (2 * (n : ℤ) + 1)
          - 2 * ((1 - (-1 : ℤ) ^ (n - 4)) * (2 * ((n : ℤ) - 2) + 1))
          + (1 - (-1 : ℤ) ^ (n - 4)) * (2 * ((n : ℤ) - 4) + 1) := by rw [h0, h2, h4]
      _ = 0 := by ring
  omega

/-! ### Step 5: Rational ordinary generating function in `PowerSeries ℚ` and full C057 bundle -/

theorem a_gf :
    ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ) *
        PowerSeries.mk (fun n => (a n : ℚ)) =
      1 + 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + PowerSeries.X ^ 4 := by
  let X : PowerSeries ℚ := PowerSeries.X
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hlhs : ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) * F =
      F - 2 * (X ^ 2 * F) + X ^ 4 * F := by ring
  change ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) * F =
      1 + 3 * X - 2 * X ^ 2 + X ^ 3 + X ^ 4
  rw [hlhs]
  apply PowerSeries.ext
  intro n
  dsimp only [X, F]
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
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
    have hne2 : k + 5 ≠ 2 := by omega
    have hne3 : k + 5 ≠ 3 := by omega
    have hne4 : k + 5 ≠ 4 := by omega
    simp only [h2, h4, hne0, hne1, hne2, hne3, hne4, ↓reduceIte,
      show k + 5 - 2 = k + 3 by omega, show k + 5 - 4 = k + 1 by omega]
    linarith

/-- Conjunction bundling all four pinned `C057` (`OEIS A266437`) theorems. -/
theorem c057_a266437_bundle :
    a 0 = 1 ∧
    (∀ n : ℕ, n > 0 → (a n : ℤ) * 2 = (1 - (-1 : ℤ) ^ n) * (2 * (n : ℤ) + 1)) ∧
    (∀ n : ℕ, n > 4 → (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
    (((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ) *
        PowerSeries.mk (fun n => (a n : ℚ)) =
      1 + 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + PowerSeries.X ^ 4) :=
  ⟨a_zero, a_closed_form, a_recurrence, a_gf⟩

/-- Michael De Vlieger's printed denominator `(-1 + X^2)^2` equals `(1 - X)^2 * (1 + X)^2`
identically in `PowerSeries ℚ`. -/
theorem a_gf_denom_eq_devlieger :
    ((-1 + PowerSeries.X ^ 2) ^ 2 : PowerSeries ℚ) =
      (1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 := by
  ring

/-- The denominator `Q(X) = (1 - X)^2 * (1 + X)^2` is a unit in `PowerSeries ℚ`
because `constantCoeff Q = 1 ≠ 0`, confirming exact equivalence of the cleared-denominator
identity `a_gf` with De Vlieger's rational generating function. -/
theorem a_gf_denom_isUnit :
    IsUnit (((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- Unit-inverse form of `a_gf`: for the unique unit `u` equal to `(1 - X)^2 * (1 + X)^2`,
`PowerSeries.mk (fun n => (a n : ℚ)) = P(X) * u⁻¹`. -/
theorem a_gf_unit_inv (u : (PowerSeries ℚ)ˣ)
    (hu : (u : PowerSeries ℚ) = ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ)) :
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
        PowerSeries.X ^ 4 : PowerSeries ℚ) * (↑u⁻¹ : PowerSeries ℚ) := by
  calc
    PowerSeries.mk (fun n => (a n : ℚ))
        = (↑u : PowerSeries ℚ) * PowerSeries.mk (fun n => (a n : ℚ)) * (↑u⁻¹ : PowerSeries ℚ) := by
          rw [mul_right_comm, Units.mul_inv, one_mul]
    _ = (1 + 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
          PowerSeries.X ^ 4 : PowerSeries ℚ) * (↑u⁻¹ : PowerSeries ℚ) := by
          rw [hu, a_gf]

/-! ### Step 6: ON/OFF complement law and 8-rule single-seed equivalence class -/

/-- OFF-cell count on `[-n, n]` for the exact same Rule 23 `ℤ`-evolution (`OEIS A266439`). -/
def aOff (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca n j))).card

/-- Exact ON/OFF partition identity across all generations `n : ℕ`:
`a n + aOff n = 2 * n + 1`. -/
theorem a_add_off (n : ℕ) : a n + aOff n = 2 * n + 1 := by
  unfold a aOff
  have hcongr :
      (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca n j)) =
        (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => ¬(ca n j = true)) := by
    apply Finset.filter_congr
    intro j _
    cases ca n j <;> simp
  rw [hcongr, Finset.card_filter_add_card_filter_not, Int.card_Icc]
  omega

/-- Generic Wolfram ECA rule evaluation by bit lookup. -/
def evalRule (code : ℕ) (l c r : Bool) : Bool :=
  Nat.testBit code (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Evolution on `ℤ` of an arbitrary Wolfram ECA rule `code` from a single ON cell at `j = 0`. -/
def caRule (code : ℕ) : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => evalRule code (caRule code n (j - 1)) (caRule code n j) (caRule code n (j + 1))

/-- Weight-2 neighborhood avoidance: from a single ON seed, every neighborhood occurring at any
generation `n : ℕ` and site `j : ℤ` has Hamming weight `0`, `1`, or `3` (never `2`). Therefore
any Wolfram ECA rule matching Rule 23 on bits `{0, 1, 2, 4, 7}` produces the exact same
spacetime lattice on `ℕ × ℤ`. -/
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
    change evalRule code (caRule code n (j - 1)) (caRule code n j) (caRule code n (j + 1)) =
      rule23 (ca n (j - 1)) (ca n j) (ca n (j + 1))
    rw [ih (j - 1), ih j, ih (j + 1)]
    cases n with
    | zero =>
      change evalRule code (decide (j - 1 = 0)) (decide (j = 0)) (decide (j + 1 = 0)) =
        rule23 (decide (j - 1 = 0)) (decide (j = 0)) (decide (j + 1 = 0))
      have hsplit : j ≤ -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
      rcases hsplit with h | rfl | rfl | rfl | h
      · rw [decide_eq_false (by omega : ¬(j - 1 = 0)),
            decide_eq_false (by omega : ¬(j = 0)),
            decide_eq_false (by omega : ¬(j + 1 = 0))]
        simpa [evalRule, rule23] using h0
      · rw [decide_eq_false (by omega : ¬((-1 : ℤ) - 1 = 0)),
            decide_eq_false (by omega : ¬((-1 : ℤ) = 0)),
            decide_eq_true (by omega : (-1 : ℤ) + 1 = 0)]
        simpa [evalRule, rule23] using h1
      · rw [decide_eq_false (by omega : ¬((0 : ℤ) - 1 = 0)),
            decide_eq_true (rfl : (0 : ℤ) = 0),
            decide_eq_false (by omega : ¬((0 : ℤ) + 1 = 0))]
        simpa [evalRule, rule23] using h2
      · rw [decide_eq_true (by omega : (1 : ℤ) - 1 = 0),
            decide_eq_false (by omega : ¬((1 : ℤ) = 0)),
            decide_eq_false (by omega : ¬((1 : ℤ) + 1 = 0))]
        simpa [evalRule, rule23] using h4
      · rw [decide_eq_false (by omega : ¬(j - 1 = 0)),
            decide_eq_false (by omega : ¬(j = 0)),
            decide_eq_false (by omega : ¬(j + 1 = 0))]
        simpa [evalRule, rule23] using h0
    | succ m =>
      have hm : 1 ≤ m + 1 := by omega
      rw [ca_eq_decide_odd (m + 1) hm (j - 1),
          ca_eq_decide_odd (m + 1) hm j,
          ca_eq_decide_odd (m + 1) hm (j + 1)]
      cases decide (Odd (m + 1))
      · simpa [evalRule, rule23] using h0
      · simpa [evalRule, rule23] using h7

/-- Exact 8-rule single-seed equivalence class (`OEIS A266434`): Rules
`23, 31, 55, 63, 87, 95, 119, 127` generate the exact same `ℤ`-evolution and `A266437` ON counts
from a single ON seed. -/
theorem caRule_equiv_class (code : ℕ)
    (hmem : code ∈ ([23, 31, 55, 63, 87, 95, 119, 127] : List ℕ)) :
    ∀ n : ℕ, ∀ j : ℤ, caRule code n j = ca n j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact caRule_eq_ca _ rfl rfl rfl rfl rfl

/-! ### Non-vacuity: Computable causal-cone mirror, OEIS spot checks, guard sharpness, and zero-padding trap -/

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

/-- Pure kernel `rfl` check of `a_dp` against `OEIS A266437` for `n = 0..12`. -/
theorem a_dp_spot_0_to_12 :
    (List.range 13).map a_dp = [1, 3, 0, 7, 0, 11, 0, 15, 0, 19, 0, 23, 0] :=
  rfl

/-- Kernel-checked agreement of the pinned `A266437.a` with `OEIS A266437` for `n = 0..12`. -/
theorem a_spot_0_to_12 :
    (List.range 13).map a = [1, 3, 0, 7, 0, 11, 0, 15, 0, 19, 0, 23, 0] := by
  have hfun : a = a_dp := funext (fun n => (a_dp_eq_a n).symm)
  rw [hfun]
  exact a_dp_spot_0_to_12

/-- Sharpness of `n > 0` in `a_closed_form`: fails at `n = 0` (`2 ≠ 0`). -/
theorem a_closed_form_false_zero :
    (a 0 : ℤ) * 2 ≠ (1 - (-1 : ℤ) ^ 0) * (2 * (0 : ℤ) + 1) := by
  norm_num [a_zero]

/-- Sharpness of `n > 4` in `a_recurrence`: fails at `n = 4` (`0 ≠ -1` in `ℤ`,
unlike saturating `ℕ` subtraction which would falsely mask `2 * 0 - 1 = 0`). -/
theorem a_recurrence_false_four :
    (a 4 : ℤ) ≠ 2 * (a 2 : ℤ) - (a 0 : ℤ) := by
  norm_num [a_four, a_two, a_zero]

/-- Growing-window zero-padded evolution (the erroneous convention noted in `PIN-C057.md`
fidelity note 4, where cells outside `[-m, m]` at step `m` are forced to `false`). -/
def caZeroPad : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | m + 1, j =>
    let get (k : ℤ) : Bool := if -(m : ℤ) ≤ k ∧ k ≤ (m : ℤ) then caZeroPad m k else false
    if -((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + 1 : ℕ) : ℤ) then
      rule23 (get (j - 1)) (get j) (get (j + 1))
    else
      false

/-- ON-cell count on `[-n, n]` under the erroneous growing-window zero-padded convention. -/
def aZeroPad (n : ℕ) : ℕ :=
  ((List.range (2 * n + 1)).filter (fun i => caZeroPad n ((i : ℤ) - (n : ℤ)))).length

/-- Kernel `rfl` confirmation of the zero-padding trap (`PIN-C057.md` fidelity note 4):
growing-window zero-padding produces window `10001` (`2` ON cells) at `n = 2`, whereas
true `ℤ`-evolution gives `a 2 = 0`. -/
theorem aZeroPad_two_eq_two : aZeroPad 2 = 2 ∧ aZeroPad 2 ≠ a 2 := by
  have h : aZeroPad 2 = 2 := rfl
  refine ⟨h, ?_⟩
  rw [h, a_two]
  omega

end A266437
