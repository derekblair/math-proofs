import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Seam C `S003` (`OEIS A385590`): Fibonacci Triangle Bijection onto `ℕ_{≥ 1}`

Formalizes and proves Werner Schulte's conjecture (`OEIS A385590`, `%C` line 11 under `%N` line 10,
live revision `#7 Jul 07 2025 20:01:36`) against the frozen contract `PIN-S003.md` v1
(`SeamC.A385590.triangle_bijective_posNat`, `delta_vs_source: NONE`), following the
cumulative-coverage and overflow-transposition blueprint `L1`–`L10` from `SCOPING-S003.md` §2.3.
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

/-! ### `L1` — Block-base definition and block-local / `ℤ`-lifted form of `T(n, k)` -/

/-- Block base `b(i) := F(i - 1)^2 + 1 - ((i - 1) % 2) = T(F(i), 1)` for `i ≥ 2`. -/
def b (i : ℕ) : ℕ :=
  F (i - 1) ^ 2 + 1 - ((i - 1) % 2)

/-- Subtraction-free form of `b(i)` for all `i ≥ 1`: `b(i) = F(i - 1)^2 + i % 2`. -/
theorem b_eq_fib_sq_add_mod {i : ℕ} (hi : 1 ≤ i) :
    b i = F (i - 1) ^ 2 + i % 2 := by
  unfold b
  omega

/-- At `n = 1`, the unique Fibonacci block index is `blockIndex 1 = 2` (`A130233(1) = 2`). -/
theorem blockIndex_one : blockIndex 1 = 2 := rfl

/-- On block `Δ_i` (`2 ≤ i`, `F(i) ≤ n < F(i + 1)`), `blockIndex n = i`. -/
theorem blockIndex_eq_of_mem_block {i n : ℕ} (hi : 2 ≤ i) (hlo : F i ≤ n) (hhi : n < F (i + 1)) :
    blockIndex n = i := by
  have hn : 1 ≤ n := le_trans (by simpa using Nat.fib_mono hi) hlo
  exact ((fibBlockIndex_existsUnique hn).unique ⟨hi, hlo, hhi⟩ (blockIndex_spec hn)).symm

/-- Block-local `ℕ` formula for `T(n, k)` on `Δ_i`. -/
theorem T_eq_blockLocal {i n k : ℕ} (hi : 2 ≤ i) (hlo : F i ≤ n) (hhi : n < F (i + 1)) :
    T n k = b i + (n - F i) * F (i - 2) + (k - 1) * F (i - 1) := by
  have hbi : blockIndex n = i := blockIndex_eq_of_mem_block hi hlo hhi
  simp only [T, b, hbi]

/-- `L1` (`ℤ`-lifted block-local formula): on `2 ≤ i`, `F(i) ≤ n < F(i + 1)`, and `1 ≤ k`,
all `ℕ` subtractions in `T(n, k)` lift cleanly to `ℤ`. -/
theorem T_cast_int_eq_blockLocal {i n k : ℕ} (hi : 2 ≤ i)
    (hlo : F i ≤ n) (hhi : n < F (i + 1)) (hk : 1 ≤ k) :
    (T n k : ℤ) = (b i : ℤ) + ((n : ℤ) - (F i : ℤ)) * (F (i - 2) : ℤ) +
      ((k : ℤ) - 1) * (F (i - 1) : ℤ) := by
  rw [T_eq_blockLocal hi hlo hhi]
  push_cast
  rw [Int.ofNat_sub hlo, Int.ofNat_sub hk]
  ring

/-! ### `L2` — Cassini's identity and consecutive-Fibonacci coprimality -/

/-- Shifted Cassini identity: `F(m + 1)^2 - F(m + 2) * F(m) = (-1)^m` for all `m : ℕ`. -/
theorem fib_cassini_shift (m : ℕ) :
    (F (m + 1) : ℤ) ^ 2 - (F (m + 2) : ℤ) * (F m : ℤ) = (-1 : ℤ) ^ m := by
  induction m with
  | zero => simp [F]
  | succ m ih =>
    have h2 : F (m + 2) = F m + F (m + 1) := Nat.fib_add_two
    have h3 : F (m + 3) = F (m + 1) + F (m + 2) := Nat.fib_add_two
    have h2z : (F (m + 2) : ℤ) = (F m : ℤ) + (F (m + 1) : ℤ) := by exact_mod_cast h2
    have h3z : (F (m + 3) : ℤ) = (F (m + 1) : ℤ) + (F (m + 2) : ℤ) := by exact_mod_cast h3
    calc
      (F (m + 2) : ℤ) ^ 2 - (F (m + 3) : ℤ) * (F (m + 1) : ℤ)
          = -((F (m + 1) : ℤ) ^ 2 - (F (m + 2) : ℤ) * (F m : ℤ)) := by
            rw [h3z, h2z]; ring
      _ = -((-1 : ℤ) ^ m) := by rw [ih]
      _ = (-1 : ℤ) ^ (m + 1) := by rw [pow_succ]; ring

/-- `L2` (`fib_cassini_and_coprime`): for every `i ≥ 2`,
`F(i - 1)^2 - F(i) * F(i - 2) = (-1)^i` and `Nat.Coprime (F(i - 1)) (F(i - 2))`. -/
theorem fib_cassini_and_coprime {i : ℕ} (hi : 2 ≤ i) :
    (F (i - 1) : ℤ) ^ 2 - (F i : ℤ) * (F (i - 2) : ℤ) = (-1 : ℤ) ^ i ∧
      Nat.Coprime (F (i - 1)) (F (i - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
  refine ⟨?_, ?_⟩
  · simpa [pow_add] using fib_cassini_shift m
  · simpa using (Nat.fib_coprime_fib_succ m).symm

/-! ### `L3` — Block-base recurrence `b(i) + F(i) * F(i - 1) = b(i + 1)` and growth -/

theorem blockBase_step {i : ℕ} (hi : 2 ≤ i) :
    b i + F i * F (i - 1) = b (i + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hb1 : b (k + 1) = F k ^ 2 + (k + 1) % 2 := b_eq_fib_sq_add_mod (by omega)
  have hb2 : b (k + 2) = F (k + 1) ^ 2 + (k + 2) % 2 := by
    simpa using b_eq_fib_sq_add_mod (i := k + 2) (by omega)
  have hfib : F (k + 2) = F k + F (k + 1) := Nat.fib_add_two
  have hfibz : (F (k + 2) : ℤ) = (F k : ℤ) + (F (k + 1) : ℤ) := by exact_mod_cast hfib
  have hcas := fib_cassini_shift k
  have hprod : (F k : ℤ) ^ 2 + (F (k + 1) : ℤ) * (F k : ℤ) =
      (F (k + 1) : ℤ) ^ 2 - (-1 : ℤ) ^ k := by
    linear_combination -hcas - (F k : ℤ) * hfibz
  have hpar : (((k + 1) % 2 : ℕ) : ℤ) - (-1 : ℤ) ^ k = (((k + 2) % 2 : ℕ) : ℤ) := by
    have hdiv : k = 2 * (k / 2) + k % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
    · have hk_even : (-1 : ℤ) ^ k = 1 := by
        rw [hdiv, h0, Nat.add_zero, pow_mul]
        norm_num
      have hm1 : (k + 1) % 2 = 1 := by omega
      have hm2 : (k + 2) % 2 = 0 := by omega
      rw [hk_even, hm1, hm2]
      norm_num
    · have hk_odd : (-1 : ℤ) ^ k = -1 := by
        rw [hdiv, h1, pow_add, pow_mul]
        norm_num
      have hm1 : (k + 1) % 2 = 0 := by omega
      have hm2 : (k + 2) % 2 = 1 := by omega
      rw [hk_odd, hm1, hm2]
      norm_num
  have hz : ((b (k + 1) + F (k + 1) * F k : ℕ) : ℤ) = (b (k + 2) : ℤ) := by
    simp only [hb1, hb2, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    linear_combination hprod + hpar
  simpa using Int.ofNat.inj hz

theorem blockBase_lt_succ {i : ℕ} (hi : 2 ≤ i) : b i < b (i + 1) := by
  rw [← blockBase_step hi]
  have h1 : 0 < F i := Nat.fib_pos.mpr (by omega)
  have h2 : 0 < F (i - 1) := Nat.fib_pos.mpr (by omega)
  have hmul : 0 < F i * F (i - 1) := Nat.mul_pos h1 h2
  omega

theorem pred_le_blockBase : ∀ {i : ℕ}, 2 ≤ i → i - 1 ≤ b i
  | 0, hi => by omega
  | 1, hi => by omega
  | 2, _ => by decide
  | m + 3, _ => by
    have ih : (m + 2) - 1 ≤ b (m + 2) := pred_le_blockBase (i := m + 2) (by omega)
    have hlt : b (m + 2) < b (m + 3) := blockBase_lt_succ (i := m + 2) (by omega)
    omega

/-- `L3` (`blockBase_succ_eq`): full recurrence, strict monotonicity, linear lower bound, and
even/odd prefix threshold formula `b(i + 1) - 1`. -/
theorem blockBase_succ_eq {i : ℕ} (hi : 2 ≤ i) :
    b i + F i * F (i - 1) = b (i + 1) ∧
      b i < b (i + 1) ∧
      i - 1 ≤ b i ∧
      b (i + 1) - 1 = (if i % 2 = 0 then F i ^ 2 else F i ^ 2 - 1) := by
  refine ⟨blockBase_step hi, blockBase_lt_succ hi, pred_le_blockBase hi, ?_⟩
  have hb : b (i + 1) = F i ^ 2 + (i + 1) % 2 := by
    simpa using b_eq_fib_sq_add_mod (i := i + 1) (by omega)
  have hpos : 0 < F i := Nat.fib_pos.mpr (by omega)
  have hsq : 1 ≤ F i ^ 2 := by
    simpa using Nat.pow_le_pow_left (Nat.succ_le_of_lt hpos) 2
  rw [hb]
  split_ifs <;> omega

/-! ### `L4` — Row endpoints `e_{i, r} = b(i + 1) + r * F(i)` and block upper bound `< b(i + 2)` -/

theorem row_endpoint_eq {i : ℕ} (hi : 2 ≤ i) (r : ℕ) :
    b i + r * F (i - 2) + (F i + r) * F (i - 1) = b (i + 1) + r * F i := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
  have hstep : b (m + 2) + F (m + 2) * F (m + 1) = b (m + 3) := by
    simpa using blockBase_step (i := m + 2) (by omega)
  have hfib : F (m + 2) = F m + F (m + 1) := Nat.fib_add_two
  change b (m + 2) + r * F m + (F (m + 2) + r) * F (m + 1) = b (m + 3) + r * F (m + 2)
  calc
    b (m + 2) + r * F m + (F (m + 2) + r) * F (m + 1)
        = (b (m + 2) + F (m + 2) * F (m + 1)) + r * (F m + F (m + 1)) := by ring
    _ = b (m + 3) + r * F (m + 2) := by rw [hstep, ← hfib]

theorem fib_succ_eq_add_pred {i : ℕ} (hi : 2 ≤ i) :
    F (i + 1) = F (i - 1) + F i := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
  simpa using (Nat.fib_add_two (n := m + 1))

/-- `L4` (`row_endpoint_and_max_lt`): one-past-the-end endpoint identity and strict bound
`b(i) ≤ T(n, k) < b(i + 2)` for every `(n, k) ∈ Δ_i`. -/
theorem row_endpoint_and_max_lt {i n k : ℕ} (hi : 2 ≤ i)
    (hlo : F i ≤ n) (hhi : n < F (i + 1)) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    b i ≤ T n k ∧ T n k < b (i + 2) := by
  rw [T_eq_blockLocal hi hlo hhi]
  refine ⟨by omega, ?_⟩
  set r := n - F i
  set c := k - 1
  have hfib_succ : F (i + 1) = F (i - 1) + F i := fib_succ_eq_add_pred hi
  have hr : r < F (i - 1) := by omega
  have hc : c < F i + r := by omega
  have hpos : 0 < F (i - 1) := Nat.fib_pos.mpr (by omega)
  have hlt_end : b i + r * F (i - 2) + c * F (i - 1) <
      b i + r * F (i - 2) + (F i + r) * F (i - 1) := by
    have hmul : c * F (i - 1) < (F i + r) * F (i - 1) :=
      Nat.mul_lt_mul_of_pos_right hc hpos
    omega
  rw [row_endpoint_eq hi r] at hlt_end
  have hr_le : r ≤ F (i + 1) := le_trans (Nat.le_of_lt hr) (Nat.fib_mono (by omega))
  have hmul_le : r * F i ≤ F (i + 1) * F i := Nat.mul_le_mul_right (F i) hr_le
  have hstep2 : b (i + 1) + F (i + 1) * F i = b (i + 2) := by
    simpa using blockBase_step (i := i + 1) (by omega)
  omega

/-! ### `L5` — Intra-block injectivity via consecutive-Fibonacci coprimality -/

private theorem block_coords_eq_of_le {i r₁ c₁ r₂ c₂ : ℕ} (hi : 2 ≤ i)
    (hr₂ : r₂ < F (i - 1)) (hle : r₁ ≤ r₂)
    (heq : b i + r₁ * F (i - 2) + c₁ * F (i - 1) = b i + r₂ * F (i - 2) + c₂ * F (i - 1)) :
    r₁ = r₂ ∧ c₁ = c₂ := by
  have hpos : 0 < F (i - 1) := Nat.fib_pos.mpr (by omega)
  have hr_mul : r₁ * F (i - 2) ≤ r₂ * F (i - 2) := Nat.mul_le_mul_right _ hle
  have hc_mul : c₂ * F (i - 1) ≤ c₁ * F (i - 1) := by omega
  have hc_le : c₂ ≤ c₁ := by
    by_contra hlt
    have : c₁ * F (i - 1) < c₂ * F (i - 1) :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hlt) hpos
    omega
  have hdiff : (r₂ - r₁) * F (i - 2) = F (i - 1) * (c₁ - c₂) := by
    have h1 : (r₂ - r₁) * F (i - 2) = r₂ * F (i - 2) - r₁ * F (i - 2) := Nat.sub_mul r₂ r₁ _
    have h2 : F (i - 1) * (c₁ - c₂) = c₁ * F (i - 1) - c₂ * F (i - 1) := by
      rw [Nat.mul_sub, Nat.mul_comm (F (i - 1)) c₁, Nat.mul_comm (F (i - 1)) c₂]
    omega
  have hdvd_mul : F (i - 1) ∣ (r₂ - r₁) * F (i - 2) := ⟨c₁ - c₂, hdiff⟩
  have hcop : Nat.Coprime (F (i - 1)) (F (i - 2)) := (fib_cassini_and_coprime hi).2
  have hdvd : F (i - 1) ∣ r₂ - r₁ := hcop.dvd_of_dvd_mul_right hdvd_mul
  have hr_sub_zero : r₂ - r₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  have hr_eq : r₁ = r₂ := by omega
  subst hr_eq
  have hc_eq_mul : c₁ * F (i - 1) = c₂ * F (i - 1) := by omega
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hpos hc_eq_mul⟩

/-- `L5` (`triangle_injective_on_block`): `T` is injective on each Fibonacci row block `Δ_i`. -/
theorem triangle_injective_on_block {i n₁ k₁ n₂ k₂ : ℕ} (hi : 2 ≤ i)
    (hlo₁ : F i ≤ n₁) (hhi₁ : n₁ < F (i + 1)) (hk₁ : 1 ≤ k₁)
    (hlo₂ : F i ≤ n₂) (hhi₂ : n₂ < F (i + 1)) (hk₂ : 1 ≤ k₂)
    (heq : T n₁ k₁ = T n₂ k₂) :
    n₁ = n₂ ∧ k₁ = k₂ := by
  rw [T_eq_blockLocal hi hlo₁ hhi₁, T_eq_blockLocal hi hlo₂ hhi₂] at heq
  have hfib_succ : F (i + 1) = F (i - 1) + F i := fib_succ_eq_add_pred hi
  have hr₁ : n₁ - F i < F (i - 1) := by omega
  have hr₂ : n₂ - F i < F (i - 1) := by omega
  rcases le_total (n₁ - F i) (n₂ - F i) with hle | hle
  · obtain ⟨hr, hc⟩ := block_coords_eq_of_le hi hr₂ hle heq
    omega
  · obtain ⟨hr, hc⟩ := block_coords_eq_of_le hi hr₁ hle heq.symm
    omega

/-! ### `L6` & `L7` — Block image, overflow set `O_i`, gap set `G_{i+1}`, and `O_i = G_{i+1}` -/

/-- Image `T(Δ_i)` of the `i`-th Fibonacci row block `Δ_i = { (n, k) | F(i) ≤ n < F(i+1), 1 ≤ k ≤ n }`. -/
def blockImage (i : ℕ) : Set ℕ :=
  { m : ℕ | ∃ n k : ℕ, F i ≤ n ∧ n < F (i + 1) ∧ 1 ≤ k ∧ k ≤ n ∧ T n k = m }

/-- Overflow set `O_i := T(Δ_i) ∩ [b(i + 1), ∞)`. -/
def overflowSet (i : ℕ) : Set ℕ :=
  { m : ℕ | m ∈ blockImage i ∧ b (i + 1) ≤ m }

/-- Next-block pre-start gap set `G_{i+1}` (indexed by `i` so `overflowSet i = nextGapSet i`). -/
def nextGapSet (i : ℕ) : Set ℕ :=
  { m : ℕ | ∃ r' u : ℕ, r' < F i ∧ 1 ≤ u ∧ u * F i ≤ r' * F (i - 1) ∧
      (m : ℤ) = (b (i + 1) : ℤ) + (r' : ℤ) * (F (i - 1) : ℤ) - (u : ℤ) * (F i : ℤ) }

/-- Characterization of `blockImage i` in block-local coordinates `(r, c)`. -/
theorem mem_blockImage_iff_coords {i m : ℕ} (hi : 2 ≤ i) :
    m ∈ blockImage i ↔
      ∃ r c : ℕ, r < F (i - 1) ∧ c < F i + r ∧ m = b i + r * F (i - 2) + c * F (i - 1) := by
  have hfib_succ : F (i + 1) = F (i - 1) + F i := fib_succ_eq_add_pred hi
  constructor
  · rintro ⟨n, k, hlo, hhi, hk1, hkn, rfl⟩
    refine ⟨n - F i, k - 1, by omega, by omega, T_eq_blockLocal hi hlo hhi⟩
  · rintro ⟨r, c, hr, hc, rfl⟩
    have hlo : F i ≤ F i + r := by omega
    have hhi : F i + r < F (i + 1) := by omega
    refine ⟨F i + r, c + 1, hlo, hhi, by omega, by omega, ?_⟩
    rw [T_eq_blockLocal hi hlo hhi]
    simp

/-- `L6` (`block_overflow_iff`): right-endpoint parameterization of `O_i` over `ℤ`. -/
theorem block_overflow_iff {i m : ℕ} (hi : 2 ≤ i) :
    m ∈ overflowSet i ↔
      ∃ r t : ℕ, r < F (i - 1) ∧ 1 ≤ t ∧ t * F (i - 1) ≤ r * F i ∧
        (m : ℤ) = (b (i + 1) : ℤ) + (r : ℤ) * (F i : ℤ) - (t : ℤ) * (F (i - 1) : ℤ) := by
  simp only [overflowSet, Set.mem_ofPred, mem_blockImage_iff_coords hi]
  constructor
  · rintro ⟨⟨r, c, hr, hc, hm_eq⟩, hbm⟩
    have hend := row_endpoint_eq hi r
    have hct : c + (F i + r - c) = F i + r := by omega
    have hsum : m + (F i + r - c) * F (i - 1) = b (i + 1) + r * F i := by
      calc
        m + (F i + r - c) * F (i - 1)
            = b i + r * F (i - 2) + (c + (F i + r - c)) * F (i - 1) := by
              rw [hm_eq]; ring
        _ = b i + r * F (i - 2) + (F i + r) * F (i - 1) := by rw [hct]
        _ = b (i + 1) + r * F i := hend
    have hsumz : (m : ℤ) + ((F i + r - c : ℕ) : ℤ) * (F (i - 1) : ℤ) =
        (b (i + 1) : ℤ) + (r : ℤ) * (F i : ℤ) := by exact_mod_cast hsum
    refine ⟨r, F i + r - c, hr, by omega, by omega, by linarith⟩
  · rintro ⟨r, t, hr, ht1, htle, hmz⟩
    have hfi_pos : 0 < F i := Nat.fib_pos.mpr (by omega)
    have hr_mul : r * F i < F (i - 1) * F i := Nat.mul_lt_mul_of_pos_right hr hfi_pos
    have ht_lt : t < F i := by
      by_contra hge
      have : F i * F (i - 1) ≤ t * F (i - 1) :=
        Nat.mul_le_mul_right _ (Nat.le_of_not_lt hge)
      rw [Nat.mul_comm (F i) (F (i - 1))] at this
      omega
    set c := F i + r - t
    have hct : c + t = F i + r := by omega
    have hend := row_endpoint_eq hi r
    have hsum : (b i + r * F (i - 2) + c * F (i - 1)) + t * F (i - 1) =
        b (i + 1) + r * F i := by
      calc
        (b i + r * F (i - 2) + c * F (i - 1)) + t * F (i - 1)
            = b i + r * F (i - 2) + (c + t) * F (i - 1) := by ring
        _ = b i + r * F (i - 2) + (F i + r) * F (i - 1) := by rw [hct]
        _ = b (i + 1) + r * F i := hend
    have hsumz : ((b i + r * F (i - 2) + c * F (i - 1) : ℕ) : ℤ) + (t : ℤ) * (F (i - 1) : ℤ) =
        (b (i + 1) : ℤ) + (r : ℤ) * (F i : ℤ) := by exact_mod_cast hsum
    have hm_eq_z : (m : ℤ) = ((b i + r * F (i - 2) + c * F (i - 1) : ℕ) : ℤ) := by linarith
    have hm_eq : m = b i + r * F (i - 2) + c * F (i - 1) := Int.ofNat.inj hm_eq_z
    have htlez : (t : ℤ) * (F (i - 1) : ℤ) ≤ (r : ℤ) * (F i : ℤ) := by exact_mod_cast htle
    have hbmz : (b (i + 1) : ℤ) ≤ (m : ℤ) := by linarith
    exact ⟨⟨r, c, hr, by omega, hm_eq⟩, Int.ofNat_le.mp hbmz⟩

/-- `L7` (`overflow_eq_next_gap`): `O_i = G_{i+1}` via the value-preserving lattice transposition
`(r, t) ↦ (F(i) - t, F(i - 1) - r)`. -/
theorem overflow_eq_next_gap {i : ℕ} (hi : 2 ≤ i) :
    overflowSet i = nextGapSet i := by
  ext m
  rw [block_overflow_iff hi]
  simp only [nextGapSet, Set.mem_ofPred]
  have hfi_pos : 0 < F i := Nat.fib_pos.mpr (by omega)
  have hfi1_pos : 0 < F (i - 1) := Nat.fib_pos.mpr (by omega)
  constructor
  · rintro ⟨r, t, hr, ht1, htle, hmz⟩
    have hr_mul : r * F i < F (i - 1) * F i := Nat.mul_lt_mul_of_pos_right hr hfi_pos
    have ht_lt : t < F i := by
      by_contra hge
      have : F i * F (i - 1) ≤ t * F (i - 1) :=
        Nat.mul_le_mul_right _ (Nat.le_of_not_lt hge)
      rw [Nat.mul_comm (F i) (F (i - 1))] at this
      omega
    have hsub1 : ((F i - t : ℕ) : ℤ) = (F i : ℤ) - (t : ℤ) := Int.ofNat_sub (Nat.le_of_lt ht_lt)
    have hsub2 : ((F (i - 1) - r : ℕ) : ℤ) = (F (i - 1) : ℤ) - (r : ℤ) :=
      Int.ofNat_sub (Nat.le_of_lt hr)
    have htlez : (t : ℤ) * (F (i - 1) : ℤ) ≤ (r : ℤ) * (F i : ℤ) := by exact_mod_cast htle
    have hgoalz : ((F (i - 1) - r : ℕ) : ℤ) * (F i : ℤ) ≤
        ((F i - t : ℕ) : ℤ) * (F (i - 1) : ℤ) := by
      rw [hsub1, hsub2]; linarith
    refine ⟨F i - t, F (i - 1) - r, by omega, by omega, by exact_mod_cast hgoalz, ?_⟩
    rw [hsub1, hsub2, hmz]
    ring
  · rintro ⟨r', u, hr', hu1, hule, hmz⟩
    have hr'_mul : r' * F (i - 1) < F i * F (i - 1) := Nat.mul_lt_mul_of_pos_right hr' hfi1_pos
    have hu_lt : u < F (i - 1) := by
      by_contra hge
      have : F (i - 1) * F i ≤ u * F i :=
        Nat.mul_le_mul_right _ (Nat.le_of_not_lt hge)
      rw [Nat.mul_comm (F (i - 1)) (F i)] at this
      omega
    have hsub1 : ((F (i - 1) - u : ℕ) : ℤ) = (F (i - 1) : ℤ) - (u : ℤ) :=
      Int.ofNat_sub (Nat.le_of_lt hu_lt)
    have hsub2 : ((F i - r' : ℕ) : ℤ) = (F i : ℤ) - (r' : ℤ) :=
      Int.ofNat_sub (Nat.le_of_lt hr')
    have hulez : (u : ℤ) * (F i : ℤ) ≤ (r' : ℤ) * (F (i - 1) : ℤ) := by exact_mod_cast hule
    have hgoalz : ((F i - r' : ℕ) : ℤ) * (F (i - 1) : ℤ) ≤
        ((F (i - 1) - u : ℕ) : ℤ) * (F i : ℤ) := by
      rw [hsub1, hsub2]; linarith
    refine ⟨F (i - 1) - u, F i - r', by omega, by omega, by exact_mod_cast hgoalz, ?_⟩
    rw [hsub1, hsub2, hmz]
    ring

/-! ### `L8` — Modular dichotomy on `[b(i + 1), b(i + 2) - 1]` -/

private theorem mod_fib_rep_unique_le {i r₁ r₂ : ℕ} {z₁ z₂ : ℤ} (hi : 2 ≤ i)
    (hr₂ : r₂ < F i) (hle : r₁ ≤ r₂)
    (heq : (r₁ : ℤ) * (F (i - 1) : ℤ) + z₁ * (F i : ℤ) =
        (r₂ : ℤ) * (F (i - 1) : ℤ) + z₂ * (F i : ℤ)) :
    r₁ = r₂ ∧ z₁ = z₂ := by
  have hfi_pos : 0 < F i := Nat.fib_pos.mpr (by omega)
  have hfi_pos_z : (0 : ℤ) < (F i : ℤ) := by exact_mod_cast hfi_pos
  have hdiffz : ((r₂ - r₁ : ℕ) : ℤ) * (F (i - 1) : ℤ) = (z₁ - z₂) * (F i : ℤ) := by
    rw [Int.ofNat_sub hle]
    linarith
  have hnonneg : 0 ≤ (z₁ - z₂) * (F i : ℤ) := by
    rw [← hdiffz]
    positivity
  have hz_nonneg : 0 ≤ z₁ - z₂ := nonneg_of_mul_nonneg_left hnonneg hfi_pos_z
  set d : ℕ := (z₁ - z₂).toNat
  have hd_cast : (d : ℤ) = z₁ - z₂ := Int.toNat_of_nonneg hz_nonneg
  have hdiff_nat : (r₂ - r₁) * F (i - 1) = F i * d := by
    have hz : (((r₂ - r₁) * F (i - 1) : ℕ) : ℤ) = ((F i * d : ℕ) : ℤ) := by
      push_cast
      rw [hd_cast, mul_comm (F i : ℤ) (z₁ - z₂)]
      exact hdiffz
    exact Int.ofNat.inj hz
  have hcop : Nat.Coprime (F i) (F (i - 1)) := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simpa using (Nat.fib_coprime_fib_succ k).symm
  have hdvd : F i ∣ r₂ - r₁ := hcop.dvd_of_dvd_mul_right ⟨d, hdiff_nat⟩
  have hr_sub : r₂ - r₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  have hr_eq : r₁ = r₂ := by omega
  subst hr_eq
  have hz_mul : (z₁ - z₂) * (F i : ℤ) = 0 := by linarith
  have hz_zero : z₁ - z₂ = 0 :=
    (mul_eq_zero.mp hz_mul).resolve_right (ne_of_gt hfi_pos_z)
  exact ⟨rfl, sub_eq_zero.mp hz_zero⟩

/-- Unique `ℤ`-decomposition modulo `F(i)`: every `x : ℤ` has at most one representation
`x = r' * F(i - 1) + z * F(i)` with `0 ≤ r' < F(i)` and `z : ℤ`. -/
theorem mod_fib_rep_unique {i r₁ r₂ : ℕ} {z₁ z₂ : ℤ} (hi : 2 ≤ i)
    (hr₁ : r₁ < F i) (hr₂ : r₂ < F i)
    (heq : (r₁ : ℤ) * (F (i - 1) : ℤ) + z₁ * (F i : ℤ) =
        (r₂ : ℤ) * (F (i - 1) : ℤ) + z₂ * (F i : ℤ)) :
    r₁ = r₂ ∧ z₁ = z₂ := by
  rcases le_total r₁ r₂ with hle | hle
  · exact mod_fib_rep_unique_le hi hr₂ hle heq
  · obtain ⟨hr, hz⟩ := mod_fib_rep_unique_le hi hr₁ hle heq.symm
    exact ⟨hr.symm, hz.symm⟩

/-- Explicit Cassini existence of `x = r' * F(i - 1) + z * F(i)` with `r' < F(i)` and `z : ℤ`. -/
theorem mod_fib_rep_exists {i : ℕ} (hi : 2 ≤ i) (x : ℤ) :
    ∃ r' : ℕ, ∃ z : ℤ, r' < F i ∧
      x = (r' : ℤ) * (F (i - 1) : ℤ) + z * (F i : ℤ) := by
  have hfi_pos : 0 < F i := Nat.fib_pos.mpr (by omega)
  have hfi_pos_z : (0 : ℤ) < (F i : ℤ) := by exact_mod_cast hfi_pos
  have hcas : (F (i - 1) : ℤ) ^ 2 - (F i : ℤ) * (F (i - 2) : ℤ) = (-1 : ℤ) ^ i :=
    (fib_cassini_and_coprime hi).1
  have hsign_sq : ((-1 : ℤ) ^ i) * ((-1 : ℤ) ^ i) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  set a : ℤ := x * (-1 : ℤ) ^ i * (F (i - 1) : ℤ)
  set r_int : ℤ := a % (F i : ℤ)
  set q : ℤ := a / (F i : ℤ)
  have hr_nonneg : 0 ≤ r_int := Int.emod_nonneg a (ne_of_gt hfi_pos_z)
  have hr_lt_z : r_int < (F i : ℤ) := Int.emod_lt_of_pos a hfi_pos_z
  have hdiv : r_int + (F i : ℤ) * q = a := Int.emod_add_mul_ediv a (F i : ℤ)
  set r' : ℕ := r_int.toNat
  have hr'_cast : (r' : ℤ) = r_int := Int.toNat_of_nonneg hr_nonneg
  have hr'_lt : r' < F i := by
    have : (r' : ℤ) < (F i : ℤ) := by rwa [hr'_cast]
    exact_mod_cast this
  refine ⟨r', -x * (-1 : ℤ) ^ i * (F (i - 2) : ℤ) + q * (F (i - 1) : ℤ), hr'_lt, ?_⟩
  rw [hr'_cast]
  have ha_def : a = x * (-1 : ℤ) ^ i * (F (i - 1) : ℤ) := rfl
  linear_combination
    -(F (i - 1) : ℤ) * hdiv + (F (i - 1) : ℤ) * ha_def -
      x * ((-1 : ℤ) ^ i) * hcas - x * hsign_sq

/-- `L8` (`mod_fib_dichotomy`): `O_i` and `T(Δ_{i+1})` are disjoint, cover `[b(i + 1), b(i + 2))`,
and `b(i + 1) ∉ O_i`. -/
theorem mod_fib_dichotomy {i : ℕ} (hi : 2 ≤ i) :
    Disjoint (overflowSet i) (blockImage (i + 1)) ∧
      (∀ m : ℕ, b (i + 1) ≤ m → m < b (i + 2) → m ∈ overflowSet i ∨ m ∈ blockImage (i + 1)) ∧
      b (i + 1) ∉ overflowSet i := by
  have hi1 : 2 ≤ i + 1 := by omega
  have hdisp : Disjoint (overflowSet i) (blockImage (i + 1)) := by
    rw [overflow_eq_next_gap hi, Set.disjoint_left]
    intro m hm_gap hm_blk
    rcases hm_gap with ⟨r₁, u, hr₁, hu1, _, hmz₁⟩
    rw [mem_blockImage_iff_coords hi1] at hm_blk
    rcases hm_blk with ⟨r₂, c', hr₂, _, hm_eq₂⟩
    simp only [Nat.add_sub_cancel] at hr₂ hm_eq₂
    have hmz₂ : (m : ℤ) = (b (i + 1) : ℤ) + (r₂ : ℤ) * (F (i - 1) : ℤ) +
        (c' : ℤ) * (F i : ℤ) := by
      have hm_eq₂' : m = b (i + 1) + r₂ * F (i - 1) + c' * F i := by
        simpa [show i + 1 - 2 = i - 1 by omega] using hm_eq₂
      exact_mod_cast hm_eq₂'
    have heq : (r₁ : ℤ) * (F (i - 1) : ℤ) + (-(u : ℤ)) * (F i : ℤ) =
        (r₂ : ℤ) * (F (i - 1) : ℤ) + (c' : ℤ) * (F i : ℤ) := by
      linarith
    obtain ⟨_, hz⟩ := mod_fib_rep_unique hi hr₁ hr₂ heq
    omega
  refine ⟨hdisp, ?_, ?_⟩
  · intro m hlo hhi
    obtain ⟨r', z, hr', hx⟩ := mod_fib_rep_exists hi ((m : ℤ) - (b (i + 1) : ℤ))
    have hmz : (m : ℤ) = (b (i + 1) : ℤ) + (r' : ℤ) * (F (i - 1) : ℤ) + z * (F i : ℤ) := by
      linarith
    rcases lt_or_ge z 0 with hz_neg | hz_nonneg
    · left
      rw [overflow_eq_next_gap hi]
      set u : ℕ := (-z).toNat
      have hu_cast : (u : ℤ) = -z := Int.toNat_of_nonneg (by linarith)
      have hu1 : 1 ≤ u := by omega
      have hlo_z : (b (i + 1) : ℤ) ≤ (m : ℤ) := by exact_mod_cast hlo
      have hule_z : (u : ℤ) * (F i : ℤ) ≤ (r' : ℤ) * (F (i - 1) : ℤ) := by
        rw [hu_cast]; linarith
      refine ⟨r', u, hr', hu1, by exact_mod_cast hule_z, ?_⟩
      rw [hu_cast, hmz]
      ring
    · right
      rw [mem_blockImage_iff_coords hi1]
      set c' : ℕ := z.toNat
      have hc'_cast : (c' : ℤ) = z := Int.toNat_of_nonneg hz_nonneg
      have hm_nat : m = b (i + 1) + r' * F (i - 1) + c' * F i := by
        have : (m : ℤ) = ((b (i + 1) + r' * F (i - 1) + c' * F i : ℕ) : ℤ) := by
          push_cast
          rw [hc'_cast]
          exact hmz
        exact Int.ofNat.inj this
      have hend : b (i + 1) + r' * F (i - 1) + (F (i + 1) + r') * F i =
          b (i + 2) + r' * F (i + 1) := by
        simpa [show i + 1 - 2 = i - 1 by omega] using row_endpoint_eq hi1 r'
      have hlt_end : b (i + 1) + r' * F (i - 1) + c' * F i <
          b (i + 1) + r' * F (i - 1) + (F (i + 1) + r') * F i := by omega
      have hfi_pos : 0 < F i := Nat.fib_pos.mpr (by omega)
      have hc'_lt : c' < F (i + 1) + r' := by
        by_contra hge
        have : (F (i + 1) + r') * F i ≤ c' * F i :=
          Nat.mul_le_mul_right _ (Nat.le_of_not_lt hge)
        omega
      refine ⟨r', c', by simpa using hr', hc'_lt, ?_⟩
      simpa [show i + 1 - 2 = i - 1 by omega] using hm_nat
  · intro hmem
    have hb_in_next : b (i + 1) ∈ blockImage (i + 1) := by
      rw [mem_blockImage_iff_coords hi1]
      have hfi_pos : 0 < F i := Nat.fib_pos.mpr (by omega)
      have hfi1_pos : 0 < F (i + 1) := Nat.fib_pos.mpr (by omega)
      exact ⟨0, 0, by simpa using hfi_pos, by omega, by simp⟩
    exact Set.disjoint_left.mp hdisp hmem hb_in_next

/-! ### `L9` — Cumulative prefix partition `⋃_{j=2}^i T(Δ_j) = [1, b(i + 1)) ⊔ O_i` -/

/-- Cumulative prefix image `U_i := ⋃_{j = 2}^i T(Δ_j)`. -/
def prefixImage (i : ℕ) : Set ℕ :=
  { m : ℕ | ∃ j : ℕ, 2 ≤ j ∧ j ≤ i ∧ m ∈ blockImage j }

theorem prefixImage_two : prefixImage 2 = {1} := by
  ext m
  simp only [prefixImage, Set.mem_ofPred, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj2, hji, n, k, hlo, hhi, hk1, hkn, rfl⟩
    have hj : j = 2 := by omega
    subst hj
    change 1 ≤ n at hlo
    change n < 2 at hhi
    have hn1 : n = 1 := by omega
    have hk_eq : k = 1 := by omega
    subst hn1; subst hk_eq
    rfl
  · rintro rfl
    refine ⟨2, le_rfl, le_rfl, 1, 1, by decide, by decide, le_rfl, le_rfl, rfl⟩

theorem overflowSet_two : overflowSet 2 = ∅ := by
  ext m
  simp only [overflowSet, Set.mem_ofPred, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨n, k, hlo, hhi, hk1, hkn, rfl⟩
  change 1 ≤ n at hlo
  change n < 2 at hhi
  have hn1 : n = 1 := by omega
  have hk_eq : k = 1 := by omega
  subst hn1; subst hk_eq
  decide

theorem prefixImage_succ {i : ℕ} (hi : 2 ≤ i) :
    prefixImage (i + 1) = prefixImage i ∪ blockImage (i + 1) := by
  ext m
  simp only [prefixImage, Set.mem_union, Set.mem_ofPred]
  constructor
  · rintro ⟨j, hj2, hji1, hm⟩
    rcases eq_or_lt_of_le hji1 with rfl | hlt
    · exact Or.inr hm
    · exact Or.inl ⟨j, hj2, by omega, hm⟩
  · rintro (⟨j, hj2, hji, hm⟩ | hm)
    · exact ⟨j, hj2, by omega, hm⟩
    · exact ⟨i + 1, by omega, le_rfl, hm⟩

theorem overflowSet_bounds {i m : ℕ} (hi : 2 ≤ i) (hm : m ∈ overflowSet i) :
    b (i + 1) ≤ m ∧ m < b (i + 2) := by
  rcases hm with ⟨⟨n, k, hlo, hhi, hk1, hkn, rfl⟩, hge⟩
  exact ⟨hge, (row_endpoint_and_max_lt hi hlo hhi hk1 hkn).2⟩

theorem one_le_of_mem_blockImage {i m : ℕ} (hi : 2 ≤ i) (hm : m ∈ blockImage i) :
    1 ≤ m := by
  rcases hm with ⟨n, k, hlo, _, _, _, rfl⟩
  have hn : 1 ≤ n := le_trans (by simpa using Nat.fib_mono hi) hlo
  exact one_le_T hn k

theorem prefixImage_eq_initial_union_overflow :
    ∀ {i : ℕ}, 2 ≤ i →
      prefixImage i = { m : ℕ | 1 ≤ m ∧ m < b (i + 1) } ∪ overflowSet i
  | 0, hi => by omega
  | 1, hi => by omega
  | 2, _ => by
    rw [prefixImage_two, overflowSet_two, Set.union_empty]
    have hb3 : b 3 = 2 := rfl
    ext m
    simp only [Set.mem_singleton_iff, Set.mem_ofPred, hb3]
    omega
  | n + 3, _ => by
    set i := n + 2
    have hi : 2 ≤ i := by omega
    have ih := prefixImage_eq_initial_union_overflow (i := n + 2) hi
    change prefixImage (i + 1) = { m : ℕ | 1 ≤ m ∧ m < b (i + 2) } ∪ overflowSet (i + 1)
    rw [prefixImage_succ hi, ih]
    have hdich := (mod_fib_dichotomy hi).2.1
    have hlt_b : b (i + 1) < b (i + 2) := blockBase_lt_succ (by omega)
    have hb_pos : 1 ≤ b (i + 1) := by
      have hpred : (i + 1) - 1 ≤ b (i + 1) := pred_le_blockBase (i := i + 1) (by omega)
      omega
    ext m
    simp only [Set.mem_union, Set.mem_ofPred]
    constructor
    · rintro ((⟨hm1, hmlt⟩ | hmov) | hmblk)
      · exact Or.inl ⟨hm1, lt_trans hmlt hlt_b⟩
      · have ⟨hge, hlt⟩ := overflowSet_bounds hi hmov
        exact Or.inl ⟨by omega, hlt⟩
      · have hm1 : 1 ≤ m := one_le_of_mem_blockImage (by omega) hmblk
        rcases lt_or_ge m (b (i + 2)) with hlt | hge
        · exact Or.inl ⟨hm1, hlt⟩
        · exact Or.inr ⟨hmblk, hge⟩
    · rintro (⟨hm1, hmlt2⟩ | ⟨hmblk, hge2⟩)
      · rcases lt_or_ge m (b (i + 1)) with hlt1 | hge1
        · exact Or.inl (Or.inl ⟨hm1, hlt1⟩)
        · rcases hdich m hge1 hmlt2 with hmov | hmblk
          · exact Or.inl (Or.inr hmov)
          · exact Or.inr hmblk
      · exact Or.inr hmblk

theorem disjoint_prefixImage_succ {i : ℕ} (hi : 2 ≤ i) :
    Disjoint (prefixImage i) (blockImage (i + 1)) := by
  rw [prefixImage_eq_initial_union_overflow hi, Set.disjoint_left]
  intro m hm_pref hm_blk
  rcases hm_blk with ⟨n, k, hlo, hhi, hk1, hkn, rfl⟩
  have hb_le : b (i + 1) ≤ T n k := (row_endpoint_and_max_lt (by omega) hlo hhi hk1 hkn).1
  rcases hm_pref with ⟨_, hlt⟩ | hmov
  · omega
  · exact Set.disjoint_left.mp (mod_fib_dichotomy hi).1 hmov ⟨n, k, hlo, hhi, hk1, hkn, rfl⟩

theorem disjoint_blockImage_of_lt {j₁ j₂ : ℕ} (hj₁ : 2 ≤ j₁) (hlt : j₁ < j₂) :
    Disjoint (blockImage j₁) (blockImage j₂) := by
  obtain ⟨i, rfl⟩ : ∃ i, j₂ = i + 1 := ⟨j₂ - 1, by omega⟩
  have hi : 2 ≤ i := by omega
  have hsub : blockImage j₁ ⊆ prefixImage i := fun m hm => ⟨j₁, hj₁, by omega, hm⟩
  exact Disjoint.mono_left hsub (disjoint_prefixImage_succ hi)

/-- `L9` (`cumulative_prefix_partition`): pairwise disjointness of all Fibonacci row-block images
`T(Δ_j)` (`j ≥ 2`), together with the exact cumulative partition
`⋃_{j = 2}^i T(Δ_j) = { 1 ≤ m < b(i + 1) } ⊔ O_i` (`O_i ⊆ [b(i + 1), b(i + 2) - 1]`). -/
theorem cumulative_prefix_partition {i : ℕ} (hi : 2 ≤ i) :
    (∀ j₁ j₂ : ℕ, 2 ≤ j₁ → j₁ ≤ i → 2 ≤ j₂ → j₂ ≤ i → j₁ ≠ j₂ →
        Disjoint (blockImage j₁) (blockImage j₂)) ∧
      prefixImage i = { m : ℕ | 1 ≤ m ∧ m < b (i + 1) } ∪ overflowSet i ∧
      Disjoint { m : ℕ | 1 ≤ m ∧ m < b (i + 1) } (overflowSet i) ∧
      (∀ m ∈ overflowSet i, b (i + 1) ≤ m ∧ m < b (i + 2)) := by
  refine ⟨?_, prefixImage_eq_initial_union_overflow hi, ?_, fun m hm => overflowSet_bounds hi hm⟩
  · intro j₁ j₂ hj₁ _ hj₂ _ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact disjoint_blockImage_of_lt hj₁ hlt
    · exact (disjoint_blockImage_of_lt hj₂ hgt).symm
  · rw [Set.disjoint_left]
    intro m ⟨_, hlt⟩ ⟨_, hge⟩
    omega

/-! ### `L10` — Main Theorem: Bijectivity of `T` onto `ℕ_{≥ 1}` (`PIN-S003.md` v1) -/

/-- Werner Schulte's conjecture on `OEIS A385590` (`%C` line 11):
the Fibonacci triangle map `T` from `{ p : ℕ × ℕ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1 }`
to `{ m : ℕ // 1 ≤ m }` is `Function.Bijective`. -/
theorem triangle_bijective_posNat :
    Function.Bijective
      (fun q : { p : ℕ × ℕ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1 } =>
        (⟨T q.val.1 q.val.2, one_le_T q.property.1 q.val.2⟩ : { m : ℕ // 1 ≤ m })) := by
  constructor
  · -- Injectivity via L1 + L9 (inter-block disjointness) + L5 (intra-block injectivity)
    intro q₁ q₂ h_eq
    have hT : T q₁.val.1 q₁.val.2 = T q₂.val.1 q₂.val.2 := congrArg Subtype.val h_eq
    rcases q₁ with ⟨⟨n₁, k₁⟩, hn₁, hk₁, hkn₁⟩
    rcases q₂ with ⟨⟨n₂, k₂⟩, hn₂, hk₂, hkn₂⟩
    dsimp only at hT hn₁ hk₁ hkn₁ hn₂ hk₂ hkn₂
    obtain ⟨hi₁, hlo₁, hhi₁⟩ := blockIndex_spec hn₁
    obtain ⟨hi₂, hlo₂, hhi₂⟩ := blockIndex_spec hn₂
    have hm₁ : T n₁ k₁ ∈ blockImage (blockIndex n₁) :=
      ⟨n₁, k₁, hlo₁, hhi₁, hk₁, hkn₁, rfl⟩
    have hm₂ : T n₁ k₁ ∈ blockImage (blockIndex n₂) :=
      ⟨n₂, k₂, hlo₂, hhi₂, hk₂, hkn₂, hT.symm⟩
    have hi_eq : blockIndex n₁ = blockIndex n₂ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Set.disjoint_left.mp (disjoint_blockImage_of_lt hi₁ hlt) hm₁ hm₂
      · exact Set.disjoint_left.mp (disjoint_blockImage_of_lt hi₂ hgt) hm₂ hm₁
    rw [← hi_eq] at hlo₂ hhi₂
    obtain ⟨rfl, rfl⟩ :=
      triangle_injective_on_block hi₁ hlo₁ hhi₁ hk₁ hlo₂ hhi₂ hk₂ hT
    rfl
  · -- Surjectivity via L9 at i = m + 2 (since m < b(m + 3) by L3)
    rintro ⟨m, hm⟩
    have hi : 2 ≤ m + 2 := by omega
    have hm_lt : m < b (m + 3) := by
      have hbound : (m + 3) - 1 ≤ b (m + 3) := pred_le_blockBase (by omega)
      omega
    have hm_pref : m ∈ prefixImage (m + 2) := by
      rw [prefixImage_eq_initial_union_overflow hi]
      exact Or.inl ⟨hm, hm_lt⟩
    rcases hm_pref with ⟨j, hj2, _, n, k, hlo, _, hk1, hkn, hT⟩
    have hn1 : 1 ≤ n := le_trans (by simpa using Nat.fib_mono hj2) hlo
    exact ⟨⟨(n, k), ⟨hn1, hk1, hkn⟩⟩, Subtype.ext hT⟩

/-! ### Kernel-Verified Structural Corollaries and `OEIS A385590` Spot Checks -/

/-- Exact least-missing law for every prefix `2..i`: every positive integer strictly below
`b(i + 1)` appears in `⋃_{j=2}^i T(Δ_j)`, whereas `b(i + 1) = T(F(i + 1), 1)` itself does not
appear until row `F(i + 1)`. -/
theorem least_missing_posNat_prefix {i : ℕ} (hi : 2 ≤ i) :
    (∀ m : ℕ, 1 ≤ m → m < b (i + 1) → m ∈ prefixImage i) ∧
      b (i + 1) ∉ prefixImage i ∧
      T (F (i + 1)) 1 = b (i + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm1 hmlt
    rw [prefixImage_eq_initial_union_overflow hi]
    exact Or.inl ⟨hm1, hmlt⟩
  · rw [prefixImage_eq_initial_union_overflow hi]
    rintro (⟨_, hlt⟩ | hmov)
    · omega
    · exact (mod_fib_dichotomy hi).2.2 hmov
  · have hi1 : 2 ≤ i + 1 := by omega
    have hlt : F (i + 1) < F (i + 2) := Nat.fib_lt_fib_succ hi1
    rw [T_eq_blockLocal hi1 le_rfl hlt]
    simp

/-- Kernel `rfl` verification of the `n = 1` boundary (`T(1, 1) = 1`) and corrected row-3 start
(`T(2, 1) = 2`, `T(3, 1) = 4`). -/
theorem T_boundary_spot_checks :
    blockIndex 1 = 2 ∧ T 1 1 = 1 ∧ T 2 1 = 2 ∧ T 2 2 = 3 ∧ T 3 1 = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Kernel `rfl` verification of all `91` entries of `OEIS A385590` `%e` (rows `1..13`). -/
theorem T_oeis_rows_1_to_13 :
    (List.range 13).map (fun r => (List.range (r + 1)).map (fun c => T (r + 1) (c + 1))) =
      [ [1],
        [2, 3],
        [4, 6, 8],
        [5, 7, 9, 11],
        [10, 13, 16, 19, 22],
        [12, 15, 18, 21, 24, 27],
        [14, 17, 20, 23, 26, 29, 32],
        [25, 30, 35, 40, 45, 50, 55, 60],
        [28, 33, 38, 43, 48, 53, 58, 63, 68],
        [31, 36, 41, 46, 51, 56, 61, 66, 71, 76],
        [34, 39, 44, 49, 54, 59, 64, 69, 74, 79, 84],
        [37, 42, 47, 52, 57, 62, 67, 72, 77, 82, 87, 92],
        [65, 73, 81, 89, 97, 105, 113, 121, 129, 137, 145, 153, 161] ] := rfl

/-- Kernel refutation witness for the naive per-block tiling sketch on `Δ_4` (rows `3..4`):
`T(Δ_4) = [4, 6, 8, 5, 7, 9, 11]` has `7 ≠ 5 = F(4)^2 - F(3)^2` entries, underflows `[5, 9]` at `4`,
overflows at `11`, and omits `10 = T(5, 1)`. -/
theorem block4_refutes_per_block_tiling :
    [T 3 1, T 3 2, T 3 3, T 4 1, T 4 2, T 4 3, T 4 4] = [4, 6, 8, 5, 7, 9, 11] ∧
      F 4 ^ 2 - F 3 ^ 2 = 5 ∧ T 5 1 = 10 :=
  ⟨rfl, rfl, rfl⟩

end SeamC.A385590
