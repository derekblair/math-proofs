import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Seam B Entry C064 (OEIS A115861 / A391736): Formal Refutation via Carry-Automaton Certificate

Formalizes and proves all four pinned headline theorems from `PIN-C064.md` v1
(`sha256: 6adc03a67107741a685c3a22bf637ae995d140bee9e235e4ae6f256055410e84`) and
`ComparatorChallenges/C064CarrylessBound.lean` with zero `sorry`, zero `native_decide`,
zero `Lean.ofReduceBool`, and standard axioms only (`propext`, `Classical.choice`, `Quot.sound`):

1. **`clMul` properties & GF(2)[X] polynomial equivalence**:
   Proves the recursive identities, `clMul a b ≤ a * b`, dyadic scaling on both arguments,
   and exact bitwise polynomial convolution equivalence (`clMul_testBit`), certifying that
   `clMul` agrees identically with `OEIS A048720`.
2. **General carry-automaton soundness (`carryEq_parity`, `carryEq_zero`,
   `carryEq_step_even`, `carryEq_step_odd`)**:
   Establishes the exact LSB-to-MSB finite-state transition equations for
   `S + m * i = R ^^^ clMul n i`.
3. **73-state kernel-checked non-existence certificate for `(n = 239, m = 215)`
   (`no_sol_lt_2pow28`)**:
   Certifies purely inside the Lean kernel (`decide` on a 73-element state list, zero
   `native_decide`) that NO integer `i` with `1 ≤ i < 2 ^ 28 = 268,435,456` satisfies
   `215 * i = clMul 239 i`. This simultaneously excludes all `1 ≤ i ≤ 239 ^ 3 = 13,651,919`
   and all `1 ≤ i ≤ 478 ^ 3 = 109,215,352`.
4. **Minimal witness and formal refutations (`c064_witness`, `c064_refutation_card`,
   `c064_refutation_pointwise`, `c064_refutation_doubling`)**:
   - Proves `215 * 302775165 = clMul 239 302775165 = 65096660475` with `302775165 > 239 ^ 3`,
     closing `c064_witness` and `c064_refutation_pointwise`.
   - Proves Karttunen's lower bound `1 + A115861 n ≤ (rowA391736Values n).ncard` for all `n ≥ 1`,
     and strict inequality `1 + A115861 239 < (rowA391736Values 239).ncard`, closing
     `c064_refutation_card` (`OEIS A391736` `%C`).
   - Proves `A115861 478 < A115861 956` via the injective doubling embedding
     `m ↦ 2 * m` plus the new witness `860 = 4 * 215` at `i = 302775165 ≤ 956 ^ 3`,
     closing `c064_refutation_doubling` (`OEIS A115861` `%F`).
5. **Secondary product identities (`c064_secondary_n4`, `c064_secondary_n5`)**:
   Kernel-verifies the product equalities for `(n = 391, m = 367, i = 186185132365 > 391 ^ 4)`
   and `(n = 511, m = 507, i = 35400328149431 > 511 ^ 5)`.
-/

namespace C064

/-- Carryless base-2 multiplication (`OEIS A048720`), corresponding to polynomial
multiplication in `GF(2)[X]` encoded in binary:
`clMul a 0 = 0`, `clMul a (2 * k) = 2 * clMul a k`, and
`clMul a (2 * k + 1) = (2 * clMul a k) ^^^ a`. -/
def clMul (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else
    let half := clMul a (b / 2)
    if b % 2 = 1 then (2 * half) ^^^ a else 2 * half

/-- The set of distinct values occurring on row `n` of `OEIS A391736`: all integers `m`
such that `m * i = A048720(n, i)` for some odd integer `i ≥ 1`. -/
def rowA391736Values (n : ℕ) : Set ℕ :=
  { m : ℕ | ∃ i : ℕ, 0 < i ∧ i % 2 = 1 ∧ m * i = clMul n i }

/-- The finite set of integers `m ∈ {1, ..., n - 1}` admitting a solution
`m * i = A048720(n, i)` with `1 ≤ i ≤ n ^ 3`. -/
def A115861_set (n : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 n).filter (fun m =>
    ((Finset.Icc 1 (n ^ 3)).filter (fun i => m * i = clMul n i)).Nonempty)

/-- `OEIS A115861(n)`: number of integers `m` in `1 .. n - 1` for which there exists
`i` in `1 .. n ^ 3` such that `m * i = A048720(n, i)`. -/
def A115861 (n : ℕ) : ℕ :=
  (A115861_set n).card

/-! ### Section 1: Bitwise XOR and `clMul` (`A048720`) Algebraic Properties -/

lemma testBit_two_mul_zero (x : ℕ) : (2 * x).testBit 0 = false := by
  rw [Nat.testBit_zero]
  simp

lemma testBit_two_mul_succ (x k : ℕ) : (2 * x).testBit (k + 1) = x.testBit k := by
  rw [Nat.testBit_succ]
  simp

lemma xor_mod_two_eq (x y : ℕ) : (x ^^^ y) % 2 = (x % 2 + y % 2) % 2 := by
  have hbit := Nat.testBit_xor x y 0
  rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at hbit
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
  rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
  rcases Nat.mod_two_eq_zero_or_one (x ^^^ y) with hxy | hxy <;>
  simp_all

lemma xor_div_two_eq (x y : ℕ) : (x ^^^ y) / 2 = (x / 2) ^^^ (y / 2) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ]

lemma two_mul_xor_two_mul (x y : ℕ) : (2 * x) ^^^ (2 * y) = 2 * (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero =>
    rw [Nat.testBit_xor, testBit_two_mul_zero, testBit_two_mul_zero, testBit_two_mul_zero]
    rfl
  | succ k =>
    rw [Nat.testBit_xor, testBit_two_mul_succ, testBit_two_mul_succ, testBit_two_mul_succ,
        Nat.testBit_xor]

lemma xor_two_mul_mod_two (R x : ℕ) : (R ^^^ (2 * x)) % 2 = R % 2 := by
  rw [xor_mod_two_eq]
  omega

lemma xor_two_mul_div_two (R x : ℕ) : (R ^^^ (2 * x)) / 2 = (R / 2) ^^^ x := by
  rw [xor_div_two_eq]
  simp

lemma xor_le_add (x y : ℕ) : x ^^^ y ≤ x + y := by
  induction x using Nat.strong_induction_on generalizing y with
  | h x ih =>
    by_cases hx : x = 0
    · subst hx; simp
    · have hlt : x / 2 < x := Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by norm_num)
      have hsub := ih (x / 2) hlt (y / 2)
      have hmod : (x ^^^ y) % 2 ≤ x % 2 + y % 2 := by
        rw [xor_mod_two_eq]
        omega
      have hdiv : (x ^^^ y) / 2 ≤ x / 2 + y / 2 := by
        rw [xor_div_two_eq]
        exact hsub
      omega

lemma clMul_zero (a : ℕ) : clMul a 0 = 0 := by
  rw [clMul]; simp

lemma clMul_pos_step {a b : ℕ} (hb : b ≠ 0) :
    clMul a b = if b % 2 = 1 then (2 * clMul a (b / 2)) ^^^ a else 2 * clMul a (b / 2) := by
  conv_lhs => unfold clMul
  simp [hb]

lemma clMul_two_mul (a b : ℕ) : clMul a (2 * b) = 2 * clMul a b := by
  by_cases hb : b = 0
  · subst hb; simp [clMul_zero]
  · rw [clMul_pos_step (by omega)]
    have hdiv : (2 * b) / 2 = b := by omega
    simp [hdiv]

lemma clMul_two_mul_add_one (a b : ℕ) : clMul a (2 * b + 1) = (2 * clMul a b) ^^^ a := by
  rw [clMul_pos_step (by omega)]
  have hdiv : (2 * b + 1) / 2 = b := by omega
  simp [hdiv]

lemma clMul_one_right (a : ℕ) : clMul a 1 = a := by
  have h := clMul_two_mul_add_one a 0
  simpa [clMul_zero] using h

lemma clMul_two_mul_left (a b : ℕ) : clMul (2 * a) b = 2 * clMul a b := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    by_cases hb : b = 0
    · subst hb; simp [clMul_zero]
    · have hlt : b / 2 < b := Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by norm_num)
      rw [clMul_pos_step hb, clMul_pos_step hb, ih (b / 2) hlt]
      split_ifs
      · exact two_mul_xor_two_mul (2 * clMul a (b / 2)) a
      · ring

lemma clMul_le_mul (a b : ℕ) : clMul a b ≤ a * b := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    by_cases hb : b = 0
    · subst hb; simp [clMul_zero]
    · have hlt : b / 2 < b := Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by norm_num)
      have hsub := ih (b / 2) hlt
      rw [clMul_pos_step hb]
      split_ifs with hodd
      · calc
          (2 * clMul a (b / 2)) ^^^ a ≤ 2 * clMul a (b / 2) + a := xor_le_add _ _
          _ ≤ 2 * (a * (b / 2)) + a := by omega
          _ = a * (2 * (b / 2) + 1) := by ring
          _ = a * b := by congr 1; omega
      · calc
          2 * clMul a (b / 2) ≤ 2 * (a * (b / 2)) := by omega
          _ = a * (2 * (b / 2)) := by ring
          _ = a * b := by congr 1; omega

lemma clMul_mod_two (a b : ℕ) : (clMul a b) % 2 = (a % 2) * (b % 2) := by
  by_cases hb : b = 0
  · subst hb; simp [clMul_zero]
  · rw [clMul_pos_step hb]
    split_ifs with hodd
    · rw [Nat.xor_comm, xor_two_mul_mod_two, hodd, mul_one]
    · have hev : b % 2 = 0 := by omega
      rw [hev, mul_zero]; omega

/-- Bitwise polynomial convolution formula in `GF(2)[X]`: bit `k` of `clMul a b` is the
XOR-sum over `j ≤ k` of `a.testBit j && b.testBit (k - j)`, certifying that `clMul` is
exactly `OEIS A048720`. -/
theorem clMul_testBit (a b k : ℕ) :
    (clMul a b).testBit k =
      (((Finset.range (k + 1)).filter (fun j => a.testBit j ∧ b.testBit (k - j))).card % 2 == 1) := by
  induction b using Nat.strong_induction_on generalizing k with
  | h b ih =>
    by_cases hb : b = 0
    · subst hb
      simp [clMul_zero]
    · have hlt : b / 2 < b := Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by norm_num)
      rw [clMul_pos_step hb]
      cases k with
      | zero =>
        have hrange : Finset.range 1 = {0} := rfl
        rw [hrange]
        by_cases hodd : b % 2 = 1
        · have hb0 : b.testBit 0 = true := by rw [Nat.testBit_zero]; simp [hodd]
          simp only [hodd, ↓reduceIte, Nat.testBit_xor, testBit_two_mul_zero, Bool.false_xor]
          cases ha : a.testBit 0 <;> simp [Finset.filter_singleton, ha, hb0]
        · have hb0 : b.testBit 0 = false := by rw [Nat.testBit_zero]; simp [hodd]
          simp [hodd, hb0]
      | succ k =>
        have hih := ih (b / 2) hlt k
        let S_full := (Finset.range (k + 2)).filter (fun j => a.testBit j ∧ b.testBit (k + 1 - j))
        let S_prev := (Finset.range (k + 1)).filter (fun j => a.testBit j ∧ (b / 2).testBit (k - j))
        have hS_split :
            S_full =
              if a.testBit (k + 1) ∧ b.testBit 0 then insert (k + 1) S_prev else S_prev := by
          ext j
          by_cases hjk : j = k + 1
          · subst hjk
            split_ifs with hcond
            · simp [S_full, hcond]
            · simp only [S_full, S_prev, Finset.mem_filter, Finset.mem_range, lt_self_iff_false,
                false_and, iff_false, not_and]
              intro _ ha hb0
              rw [Nat.sub_self] at hb0
              exact hcond ⟨ha, hb0⟩
          · split_ifs with hcond
            · simp only [S_full, S_prev, Finset.mem_insert, hjk, false_or, Finset.mem_filter,
                Finset.mem_range]
              constructor
              · rintro ⟨hjlt, ha, hb'⟩
                have hsub : k + 1 - j = (k - j) + 1 := by omega
                rw [hsub, Nat.testBit_succ] at hb'
                exact ⟨by omega, ha, hb'⟩
              · rintro ⟨hjlt, ha, hb'⟩
                have hsub : k + 1 - j = (k - j) + 1 := by omega
                refine ⟨by omega, ha, ?_⟩
                rw [hsub, Nat.testBit_succ]
                exact hb'
            · simp only [S_full, S_prev, Finset.mem_filter, Finset.mem_range]
              constructor
              · rintro ⟨hjlt, ha, hb'⟩
                have hsub : k + 1 - j = (k - j) + 1 := by omega
                rw [hsub, Nat.testBit_succ] at hb'
                exact ⟨by omega, ha, hb'⟩
              · rintro ⟨hjlt, ha, hb'⟩
                have hsub : k + 1 - j = (k - j) + 1 := by omega
                refine ⟨by omega, ha, ?_⟩
                rw [hsub, Nat.testBit_succ]
                exact hb'
        have hnotmem : k + 1 ∉ S_prev := by
          simp [S_prev]
        have hcard :
            S_full.card = S_prev.card + if a.testBit (k + 1) ∧ b.testBit 0 then 1 else 0 := by
          rw [hS_split]
          split_ifs
          · rw [Finset.card_insert_of_notMem hnotmem]
          · simp
        change (if b % 2 = 1 then (2 * clMul a (b / 2)) ^^^ a else 2 * clMul a (b / 2)).testBit (k + 1) =
            (S_full.card % 2 == 1)
        rw [hcard]
        by_cases hodd : b % 2 = 1
        · have hb0 : b.testBit 0 = true := by rw [Nat.testBit_zero]; simp [hodd]
          simp only [hodd, ↓reduceIte, Nat.testBit_xor, testBit_two_mul_succ, hih, hb0, and_true]
          change ((S_prev.card % 2 == 1) ^^ a.testBit (k + 1)) =
              ((S_prev.card + if a.testBit (k + 1) = true then 1 else 0) % 2 == 1)
          cases ha : a.testBit (k + 1) <;>
          rcases Nat.mod_two_eq_zero_or_one S_prev.card with hc | hc <;>
          simp [hc]
          all_goals omega
        · have hb0 : b.testBit 0 = false := by rw [Nat.testBit_zero]; simp [hodd]
          simp only [hodd, ↓reduceIte, testBit_two_mul_succ, hih, hb0]
          change (S_prev.card % 2 == 1) =
              ((S_prev.card + if a.testBit (k + 1) = true ∧ false = true then 1 else 0) % 2 == 1)
          simp

/-! ### Section 2: Zero-Recursion Pure-Arithmetic Evaluators (`xor9`, `checkClMulChain`) -/

/-- Flat, non-recursive 9-bit XOR using only GMP kernel arithmetic primitives
(`div`, `mod`, `mul`, `add`). Avoids `WellFounded.fix` and call-by-name thunk
duplication during kernel reduction (`rfl` / `decide`). -/
def xor9 (x y : ℕ) : ℕ :=
  ((x % 2 + y % 2) % 2)
  + 2 * (((x / 2) % 2 + (y / 2) % 2) % 2)
  + 4 * (((x / 4) % 2 + (y / 4) % 2) % 2)
  + 8 * (((x / 8) % 2 + (y / 8) % 2) % 2)
  + 16 * (((x / 16) % 2 + (y / 16) % 2) % 2)
  + 32 * (((x / 32) % 2 + (y / 32) % 2) % 2)
  + 64 * (((x / 64) % 2 + (y / 64) % 2) % 2)
  + 128 * (((x / 128) % 2 + (y / 128) % 2) % 2)
  + 256 * (((x / 256) % 2 + (y / 256) % 2) % 2)

lemma xor_step (x y : ℕ) : x ^^^ y = 2 * ((x / 2) ^^^ (y / 2)) + (x % 2 + y % 2) % 2 := by
  have hdiv := xor_div_two_eq x y
  have hmod := xor_mod_two_eq x y
  omega

lemma xor_low_9 (x a : ℕ) (ha : a < 512) : x ^^^ a = 512 * (x / 512) + xor9 x a := by
  have hdiv : ∀ n k, (n / k) / 2 = n / (k * 2) := fun n k => Nat.div_div_eq_div_mul n k 2
  have ha0 : a / 512 = 0 := by omega
  rw [xor_step x a]
  rw [xor_step (x / 2) (a / 2), hdiv x 2, hdiv a 2]
  rw [xor_step (x / 4) (a / 4), hdiv x 4, hdiv a 4]
  rw [xor_step (x / 8) (a / 8), hdiv x 8, hdiv a 8]
  rw [xor_step (x / 16) (a / 16), hdiv x 16, hdiv a 16]
  rw [xor_step (x / 32) (a / 32), hdiv x 32, hdiv a 32]
  rw [xor_step (x / 64) (a / 64), hdiv x 64, hdiv a 64]
  rw [xor_step (x / 128) (a / 128), hdiv x 128, hdiv a 128]
  rw [xor_step (x / 256) (a / 256), hdiv x 256, hdiv a 256]
  norm_num only
  rw [ha0, Nat.xor_zero]
  unfold xor9
  ring

lemma xor9_eq_xor {x a : ℕ} (hx : x < 512) (ha : a < 512) : xor9 x a = x ^^^ a := by
  have h := xor_low_9 x a ha
  have hx0 : x / 512 = 0 := by omega
  omega

/-- Pure-Boolean step checker for a verified `clMul a b = v` multiplication chain
`[(b₁, v₁), ..., (b_k, v_k)]` starting from `(0, 0)`. Every intermediate value is a
concrete literal, so kernel evaluation performs O(k) flat `xor9` evaluations. -/
def checkClMulChain (a : ℕ) : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | _, _, [] => true
  | bp, vp, (b, v) :: rest =>
    (if b == 2 * bp then v == 2 * vp
     else if b == 2 * bp + 1 then v == 512 * ((2 * vp) / 512) + xor9 (2 * vp) a
     else false) && checkClMulChain a b v rest

lemma clMul_of_chain_aux {a : ℕ} (ha : a < 512) :
    ∀ (rest : List (ℕ × ℕ)) (bp vp : ℕ),
      clMul a bp = vp →
      checkClMulChain a bp vp rest = true →
      ∀ p ∈ rest, clMul a p.1 = p.2 := by
  intro rest
  induction rest with
  | nil => intro _ _ _ _ _ hp; cases hp
  | cons hd tl ih =>
    rcases hd with ⟨b, v⟩
    intro bp vp hprev hchk p hp
    simp only [checkClMulChain, Bool.and_eq_true] at hchk
    rcases hchk with ⟨hstep, htl⟩
    have hbv : clMul a b = v := by
      by_cases h0 : b == 2 * bp
      · simp only [h0, ↓reduceIte, beq_iff_eq] at hstep
        have hb : b = 2 * bp := beq_iff_eq.mp h0
        rw [hb, clMul_two_mul, hprev, hstep]
      · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hstep
        by_cases h1 : b == 2 * bp + 1
        · simp only [h1, ↓reduceIte, beq_iff_eq] at hstep
          have hb : b = 2 * bp + 1 := beq_iff_eq.mp h1
          rw [hb, clMul_two_mul_add_one, hprev, xor_low_9 (2 * vp) a ha, hstep]
        · simp [h1] at hstep
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp'
    · exact hbv
    · exact ih b v hbv htl p hp'

lemma clMul_of_chain {a b v : ℕ} (ha : a < 512) (chain : List (ℕ × ℕ))
    (hchk : checkClMulChain a 0 0 chain = true) (hmem : (b, v) ∈ chain) :
    clMul a b = v :=
  clMul_of_chain_aux ha chain 0 0 (clMul_zero a) hchk (b, v) hmem

/-! ### Section 3: General Carry-Automaton Soundness -/

lemma carryEq_parity {n m S R i : ℕ} (hn : n % 2 = 1) (hm : m % 2 = 1)
    (h : S + m * i = R ^^^ clMul n i) : S % 2 = R % 2 := by
  have hmod := congrArg (· % 2) h
  rw [xor_mod_two_eq, clMul_mod_two, hn] at hmod
  have hm_mul : (m * i) % 2 = i % 2 := by
    rw [Nat.mul_mod, hm]
    omega
  rw [Nat.add_mod, hm_mul] at hmod
  omega

lemma carryEq_zero {n m S R : ℕ} (h : S + m * 0 = R ^^^ clMul n 0) : S = R := by
  simpa [clMul_zero] using h

lemma carryEq_step_even {n m S R j : ℕ}
    (h : S + m * (2 * j) = R ^^^ clMul n (2 * j)) :
    S / 2 + m * j = (R / 2) ^^^ clMul n j := by
  have hdiv := congrArg (· / 2) h
  rw [clMul_two_mul, xor_two_mul_div_two] at hdiv
  have hlhs : (S + m * (2 * j)) / 2 = S / 2 + m * j := by
    have heq : S + m * (2 * j) = S + 2 * (m * j) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by norm_num)]
  rw [hlhs] at hdiv
  exact hdiv

lemma carryEq_step_odd {n m S R j : ℕ}
    (h : S + m * (2 * j + 1) = R ^^^ clMul n (2 * j + 1)) :
    (S + m) / 2 + m * j = ((R ^^^ n) / 2) ^^^ clMul n j := by
  have hdiv := congrArg (· / 2) h
  have hrhs : R ^^^ clMul n (2 * j + 1) = (R ^^^ n) ^^^ (2 * clMul n j) := by
    rw [clMul_two_mul_add_one, Nat.xor_comm (2 * clMul n j) n, ← Nat.xor_assoc]
  rw [hrhs, xor_two_mul_div_two] at hdiv
  have hlhs : (S + m * (2 * j + 1)) / 2 = (S + m) / 2 + m * j := by
    have heq : S + m * (2 * j + 1) = (S + m) + 2 * (m * j) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by norm_num)]
  rw [hlhs] at hdiv
  exact hdiv

/-! ### Section 4: 73-State Kernel Certificate for `(n = 239, m = 215)` -/

/-- The exact 73 reachable carry-automaton states `(S, R, layer, next0Idx, next1Idx)` for
`(n = 239, m = 215)` at BFS layers `0 .. 27` starting from `(107, 119, 0)` (index `0`).
Every state in this table satisfies `S ≠ R`, and every parity-valid transition out of
layers `0 .. 26` lands at the explicitly indexed row with depth `≤ layer + 1`. The unique
accepting state at layer `28` is `(121, 121)`. -/
def certRows : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (107, 119, 0, 1, 0), (53, 59, 1, 0, 2), (134, 106, 2, 3, 4), (67, 53, 3, 0, 6),
  (174, 66, 3, 5, 7), (87, 33, 4, 0, 10), (141, 109, 4, 8, 0), (194, 86, 4, 9, 11),
  (70, 54, 5, 12, 15), (97, 43, 5, 0, 16), (151, 103, 5, 13, 0), (204, 92, 5, 14, 17),
  (35, 27, 6, 18, 0), (75, 51, 6, 19, 0), (102, 46, 6, 20, 22), (142, 108, 6, 0, 0),
  (156, 98, 6, 0, 0), (209, 89, 6, 21, 0), (17, 13, 7, 23, 0), (37, 25, 7, 24, 0),
  (51, 23, 7, 25, 0), (104, 44, 7, 26, 27), (158, 96, 7, 0, 0), (8, 6, 8, 0, 0),
  (18, 12, 8, 0, 0), (25, 11, 8, 0, 28), (52, 22, 8, 0, 0), (159, 97, 8, 0, 29),
  (120, 114, 9, 0, 0), (187, 71, 9, 30, 0), (93, 35, 10, 0, 31), (154, 102, 11, 32, 33),
  (77, 51, 12, 0, 35), (184, 68, 12, 34, 36), (92, 34, 13, 0, 0), (146, 110, 13, 37, 38),
  (199, 85, 13, 0, 39), (73, 55, 14, 0, 41), (180, 64, 14, 40, 42), (207, 93, 14, 0, 43),
  (90, 32, 15, 0, 0), (144, 108, 15, 44, 45), (197, 87, 15, 0, 46), (211, 89, 15, 0, 47),
  (72, 54, 16, 0, 0), (179, 65, 16, 0, 42), (206, 92, 16, 0, 0), (213, 91, 16, 0, 48),
  (214, 90, 17, 49, 48), (107, 45, 18, 0, 50), (161, 97, 19, 51, 0), (80, 48, 20, 52, 53),
  (40, 24, 21, 54, 55), (147, 111, 21, 37, 0), (20, 12, 22, 56, 58), (127, 123, 22, 57, 0),
  (10, 6, 23, 59, 61), (63, 61, 23, 0, 62), (117, 113, 23, 60, 0), (5, 3, 24, 0, 64),
  (58, 56, 24, 0, 0), (112, 116, 24, 63, 65), (139, 105, 24, 0, 66), (56, 58, 25, 0, 0),
  (110, 118, 25, 67, 68), (163, 77, 25, 0, 69), (177, 67, 25, 0, 70), (55, 59, 26, 71, 0),
  (162, 76, 26, 0, 0), (189, 81, 26, 72, 0), (196, 86, 26, 0, 0), (27, 29, 27, 0, 0),
  (94, 40, 27, 0, 0)
]

/-- O(73) indexed Boolean certificate checker using GMP primitives (`Nat.ble`, `==`, `xor9`),
verifying non-acceptance, `R < 256`, and indexed transition closure across all 73 rows. -/
def checkCertRow (row : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  let (S, R, k, i0, i1) := row
  Nat.ble k 27 && Nat.ble R 255 && !(S == R) &&
  (if Nat.ble (k + 1) 27 then
    let s0 := S / 2
    let r0 := R / 2
    let s1 := (S + 215) / 2
    let r1 := (xor9 R 239) / 2
    let t0 := certRows.getD i0 (0, 0, 99, 0, 0)
    let t1 := certRows.getD i1 (0, 0, 99, 0, 0)
    (!(s0 % 2 == r0 % 2) ||
      (Nat.ble (i0 + 1) 73 && t0.1 == s0 && t0.2.1 == r0 && Nat.ble t0.2.2.1 (k + 1))) &&
    (!(s1 % 2 == r1 % 2) ||
      (Nat.ble (i1 + 1) 73 && t1.1 == s1 && t1.2.1 == r1 && Nat.ble t1.2.2.1 (k + 1)))
  else true)

def checkCert : Bool :=
  certRows.all checkCertRow

/-- Pure-kernel `rfl` proof of `checkCert = true` (zero `native_decide`). -/
theorem checkCert_eq_true : checkCert = true := rfl

lemma certRows_length : certRows.length = 73 := rfl

lemma cert_row_props {S R k i0 i1 : ℕ} (hmem : (S, R, k, i0, i1) ∈ certRows) :
    k ≤ 27 ∧ S ≠ R ∧
    (k < 27 → (S / 2) % 2 = (R / 2) % 2 →
      ∃ k' j0 j1, k' ≤ k + 1 ∧ (S / 2, R / 2, k', j0, j1) ∈ certRows) ∧
    (k < 27 → ((S + 215) / 2) % 2 = ((R ^^^ 239) / 2) % 2 →
      ∃ k' j0 j1, k' ≤ k + 1 ∧ ((S + 215) / 2, (R ^^^ 239) / 2, k', j0, j1) ∈ certRows) := by
  have hall := List.all_eq_true.mp checkCert_eq_true (S, R, k, i0, i1) hmem
  simp only [checkCertRow, Bool.and_eq_true, Bool.not_eq_true',
    Nat.ble_eq, beq_eq_false_iff_ne] at hall
  rcases hall with ⟨⟨⟨hk, hRle⟩, hne⟩, htrans⟩
  have hxor : xor9 R 239 = R ^^^ 239 := xor9_eq_xor (by omega) (by norm_num)
  refine ⟨hk, hne, ?_, ?_⟩
  · intro hklt hpar
    have hk1 : k + 1 ≤ 27 := by omega
    simp only [hk1, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Nat.ble_eq, beq_iff_eq, beq_eq_false_iff_ne] at htrans
    rcases htrans.1 with hbad | ⟨⟨⟨hi0, hs0⟩, hr0⟩, hk'⟩
    · exact absurd hpar hbad
    · have hi0lt : i0 < certRows.length := by rw [certRows_length]; omega
      have hget : certRows.getD i0 (0, 0, 99, 0, 0) = certRows[i0] := List.getD_eq_getElem _ _ hi0lt
      have hmem' : certRows[i0] ∈ certRows := List.getElem_mem hi0lt
      rcases hrow : certRows[i0] with ⟨S', R', k', j0, j1⟩
      rw [hget, hrow] at hs0 hr0 hk'
      rw [hrow] at hmem'
      subst hs0; subst hr0
      exact ⟨k', j0, j1, hk', hmem'⟩
  · intro hklt hpar
    have hk1 : k + 1 ≤ 27 := by omega
    simp only [hk1, ↓reduceIte, hxor, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Nat.ble_eq, beq_iff_eq, beq_eq_false_iff_ne] at htrans
    rcases htrans.2 with hbad | ⟨⟨⟨hi1, hs1⟩, hr1⟩, hk'⟩
    · exact absurd hpar hbad
    · have hi1lt : i1 < certRows.length := by rw [certRows_length]; omega
      have hget : certRows.getD i1 (0, 0, 99, 0, 0) = certRows[i1] := List.getD_eq_getElem _ _ hi1lt
      have hmem' : certRows[i1] ∈ certRows := List.getElem_mem hi1lt
      rcases hrow : certRows[i1] with ⟨S', R', k', j0, j1⟩
      rw [hget, hrow] at hs1 hr1 hk'
      rw [hrow] at hmem'
      subst hs1; subst hr1
      exact ⟨k', j0, j1, hk', hmem'⟩

/-- Core automaton impossibility theorem: no row `(S, R, k, i0, i1) ∈ certRows` admits a
solution `S + 215 * j = R ^^^ clMul 239 j` with `j < 2 ^ (27 - k)`. -/
theorem no_carryEq_of_mem_cert :
    ∀ j S R k i0 i1 : ℕ, (S, R, k, i0, i1) ∈ certRows → j < 2 ^ (27 - k) →
      S + 215 * j ≠ R ^^^ clMul 239 j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro S R k i0 i1 hmem hj heq
    have ⟨hk_le, hne, hstep0, hstep1⟩ := cert_row_props hmem
    by_cases hj0 : j = 0
    · subst hj0
      exact hne (carryEq_zero heq)
    · have hklt : k < 27 := by
        rcases Nat.eq_or_lt_of_le hk_le with rfl | hlt
        · exfalso
          simp at hj
          exact hj0 hj
        · exact hlt
      have hj_div_lt : j / 2 < j := Nat.div_lt_self (Nat.pos_of_ne_zero hj0) (by norm_num)
      have hj_pow : j / 2 < 2 ^ (27 - (k + 1)) := by
        have hpow : 2 ^ (27 - k) = 2 * 2 ^ (27 - (k + 1)) := by
          have hexp : 27 - k = (27 - (k + 1)) + 1 := by omega
          rw [hexp, pow_succ']
        omega
      rcases Nat.mod_two_eq_zero_or_one j with hev | hodd
      · have hj_eq : j = 2 * (j / 2) := by omega
        rw [hj_eq] at heq
        have heq' := carryEq_step_even heq
        have hpar := carryEq_parity (n := 239) (m := 215) (by norm_num) (by norm_num) heq'
        obtain ⟨k', j0, j1, hk'le, hmem'⟩ := hstep0 hklt hpar
        have hj' : j / 2 < 2 ^ (27 - k') :=
          lt_of_lt_of_le hj_pow (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact ih (j / 2) hj_div_lt (S / 2) (R / 2) k' j0 j1 hmem' hj' heq'
      · have hj_eq : j = 2 * (j / 2) + 1 := by omega
        rw [hj_eq] at heq
        have heq' := carryEq_step_odd heq
        have hpar := carryEq_parity (n := 239) (m := 215) (by norm_num) (by norm_num) heq'
        obtain ⟨k', j0, j1, hk'le, hmem'⟩ := hstep1 hklt hpar
        have hj' : j / 2 < 2 ^ (27 - k') :=
          lt_of_lt_of_le hj_pow (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact ih (j / 2) hj_div_lt ((S + 215) / 2) ((R ^^^ 239) / 2) k' j0 j1 hmem' hj' heq'

/-- Sharp odd non-existence theorem: no odd `i < 2 ^ 28` satisfies `215 * i = clMul 239 i`. -/
theorem no_odd_sol_lt_2pow28 (i : ℕ) (hodd : i % 2 = 1) (hlt : i < 2 ^ 28) :
    215 * i ≠ clMul 239 i := by
  intro heq
  have hi_eq : i = 2 * (i / 2) + 1 := by omega
  have h0 : 0 + 215 * (2 * (i / 2) + 1) = 0 ^^^ clMul 239 (2 * (i / 2) + 1) := by
    simpa [← hi_eq] using heq
  have h1 := carryEq_step_odd h0
  have h1' : 107 + 215 * (i / 2) = 119 ^^^ clMul 239 (i / 2) := by
    simpa using h1
  have hstart : (107, 119, 0, 1, 0) ∈ certRows := by simp [certRows]
  have hjlt : i / 2 < 2 ^ (27 - 0) := by omega
  exact no_carryEq_of_mem_cert (i / 2) 107 119 0 1 0 hstart hjlt h1'

/-- Sharp general non-existence theorem: NO integer `i` (odd or even) with
`1 ≤ i < 2 ^ 28 = 268,435,456` satisfies `215 * i = clMul 239 i`. -/
theorem no_sol_lt_2pow28 :
    ∀ i : ℕ, 1 ≤ i → i < 2 ^ 28 → 215 * i ≠ clMul 239 i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi1 hlt
    rcases Nat.mod_two_eq_zero_or_one i with hev | hodd
    · intro heq
      have hi_eq : i = 2 * (i / 2) := by omega
      have hdiv_lt : i / 2 < i := by omega
      have hdiv_ge1 : 1 ≤ i / 2 := by omega
      have hdiv_bound : i / 2 < 2 ^ 28 := by omega
      rw [hi_eq, clMul_two_mul] at heq
      have hhalf : 215 * (i / 2) = clMul 239 (i / 2) := by omega
      exact ih (i / 2) hdiv_lt hdiv_ge1 hdiv_bound hhalf
    · exact no_odd_sol_lt_2pow28 i hodd hlt

/-! ### Section 5: Headline Witness and Refutation Theorems -/

def chain_239 : List (ℕ × ℕ) := [
  (1, 239), (2, 478), (4, 956), (9, 1943),
  (18, 3886), (36, 7772), (72, 15544), (144, 31088),
  (288, 62176), (577, 124207), (1154, 248414), (2309, 496723),
  (4619, 993353), (9239, 1986685), (18479, 3973141), (36959, 7946437),
  (73919, 15892837), (147839, 31785509), (295678, 63571018), (591357, 127142011),
  (1182715, 254283801), (2365430, 508567602), (4730861, 1017135243), (9461723, 2034270713),
  (18923447, 4068541213), (37846895, 8137082581), (75693791, 16274165061), (151387582, 32548330122),
  (302775165, 65096660475)
]

lemma clMul_239_302775165 : clMul 239 302775165 = 65096660475 :=
  clMul_of_chain (by norm_num) chain_239 rfl (by simp [chain_239])

/-- Minimal counterexample witness `(n, m, i) = (239, 215, 302775165)`:
`215 * 302775165 = A048720(239, 302775165) = 65096660475` with `302775165 > 239 ^ 3 = 13651919`,
while NO integer `i` in `1 .. 239 ^ 3` satisfies `215 * i = A048720(239, i)`. -/
theorem c064_witness :
    1 ≤ 215 ∧ 215 < 239 ∧ 239 ^ 3 < 302775165 ∧ 302775165 % 2 = 1 ∧
    215 * 302775165 = clMul 239 302775165 ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 239 ^ 3 → 215 * i ≠ clMul 239 i) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [clMul_239_302775165]
  · intro i hi1 hle
    exact no_sol_lt_2pow28 i hi1 (by omega)

/-- Any positive solution `m * i = clMul n i` reduces (by stripping factors of `2` from `i`)
to an odd positive solution `i₀ ≤ i` with `m * i₀ = clMul n i₀`. -/
lemma odd_solution_of_solution {n m : ℕ} :
    ∀ i : ℕ, 0 < i → m * i = clMul n i →
      ∃ i₀ : ℕ, 0 < i₀ ∧ i₀ ≤ i ∧ i₀ % 2 = 1 ∧ m * i₀ = clMul n i₀ := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi heq
    rcases Nat.mod_two_eq_zero_or_one i with hev | hodd
    · have hi_eq : i = 2 * (i / 2) := by omega
      rw [hi_eq, clMul_two_mul] at heq
      have h2 : 2 * (m * (i / 2)) = 2 * clMul n (i / 2) := by rw [← heq]; ring
      have hhalf : m * (i / 2) = clMul n (i / 2) := by omega
      obtain ⟨i₀, hi₀pos, hi₀le, hi₀odd, hi₀eq⟩ := ih (i / 2) (by omega) (by omega) hhalf
      exact ⟨i₀, hi₀pos, by omega, hi₀odd, hi₀eq⟩
    · exact ⟨i, hi, le_refl i, hodd, heq⟩

lemma rowA391736Values_finite (n : ℕ) : (rowA391736Values n).Finite := by
  apply (Set.finite_le_nat n).subset
  rintro m ⟨i, hi, _, heq⟩
  have hle : m * i ≤ n * i := by
    rw [heq]
    exact clMul_le_mul n i
  exact Nat.le_of_mul_le_mul_right hle hi

lemma mem_rowA391736Values_self (n : ℕ) : n ∈ rowA391736Values n :=
  ⟨1, by norm_num, by norm_num, by simp [clMul_one_right]⟩

lemma mem_A115861_set_iff (n m : ℕ) :
    m ∈ A115861_set n ↔ (0 < m ∧ m < n) ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ^ 3 ∧ m * i = clMul n i := by
  simp only [A115861_set, Finset.mem_filter, Finset.mem_Ioo, Finset.filter_nonempty_iff,
    Finset.mem_Icc, and_assoc]

lemma A115861_set_subset_rowA391736 (n : ℕ) :
    (A115861_set n : Set ℕ) ⊆ rowA391736Values n := by
  intro m hm
  rw [Finset.mem_coe, mem_A115861_set_iff] at hm
  rcases hm with ⟨_, ⟨i, hi1, _, heq⟩⟩
  obtain ⟨i₀, hi₀pos, _, hi₀odd, hi₀eq⟩ := odd_solution_of_solution i (by omega) heq
  exact ⟨i₀, hi₀pos, hi₀odd, hi₀eq⟩

/-- Karttunen's lower bound (`A115861` `%C` / `A391736` `%C`): for every `n ≥ 1`,
row `n` of `A391736` contains at least `1 + A115861(n)` distinct values. -/
theorem rowA391736_card_ge (n : ℕ) : 1 + A115861 n ≤ (rowA391736Values n).ncard := by
  let S : Finset ℕ := insert n (A115861_set n)
  have hsub : (S : Set ℕ) ⊆ rowA391736Values n := by
    intro m hm
    simp only [S, Finset.coe_insert, Set.mem_insert_iff] at hm
    rcases hm with rfl | hm'
    · exact mem_rowA391736Values_self m
    · exact A115861_set_subset_rowA391736 n hm'
  have hnotmem : n ∉ A115861_set n := by
    rw [mem_A115861_set_iff]; omega
  have hcard : S.card = 1 + A115861 n := by
    dsimp only [S, A115861]
    rw [Finset.card_insert_of_notMem hnotmem]
    omega
  have hle := Set.ncard_le_ncard hsub (rowA391736Values_finite n)
  rw [Set.ncard_coe_finset, hcard] at hle
  exact hle

/-- General strict-inequality lemma: whenever some `m ≠ n` lies on row `n` of `A391736`
but not in `A115861_set n`, row `n` has strictly more than `1 + A115861(n)` distinct values. -/
lemma rowA391736_card_gt_of_new {n m : ℕ} (hm_in : m ∈ rowA391736Values n)
    (hm_ne : m ≠ n) (hm_not : m ∉ A115861_set n) :
    1 + A115861 n < (rowA391736Values n).ncard := by
  let S : Finset ℕ := insert m (insert n (A115861_set n))
  have hn_not : n ∉ A115861_set n := by
    rw [mem_A115861_set_iff]; omega
  have hm_not_ins : m ∉ insert n (A115861_set n) := by
    rw [Finset.mem_insert]
    rintro (rfl | h)
    · exact hm_ne rfl
    · exact hm_not h
  have hsub : (S : Set ℕ) ⊆ rowA391736Values n := by
    intro x hx
    simp only [S, Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | rfl | hx'
    · exact hm_in
    · exact mem_rowA391736Values_self x
    · exact A115861_set_subset_rowA391736 n hx'
  have hcard : S.card = 2 + A115861 n := by
    dsimp only [S, A115861]
    rw [Finset.card_insert_of_notMem hm_not_ins, Finset.card_insert_of_notMem hn_not]
    omega
  have hle := Set.ncard_le_ncard hsub (rowA391736Values_finite n)
  rw [Set.ncard_coe_finset, hcard] at hle
  omega

/-- Strict inequality at `n = 239`: row `239` of `A391736` has at least
`2 + A115861(239)` distinct values (missing `m = 215` below `239 ^ 3`). -/
theorem rowA391736_239_gt : 1 + A115861 239 < (rowA391736Values 239).ncard := by
  have hw := c064_witness
  refine rowA391736_card_gt_of_new (n := 239) (m := 215)
    ⟨302775165, by norm_num, hw.2.2.2.1, hw.2.2.2.2.1⟩ (by norm_num) ?_
  rw [mem_A115861_set_iff]
  rintro ⟨_, i, hi1, hile, heq⟩
  exact hw.2.2.2.2.2 i hi1 hile heq

/-- Formal refutation of `OEIS A391736` `%C`: `1 + A115861(n)` is NOT in general equal to
the exact number of distinct values occurring on row `n` of `A391736` (fails at `n = 239`). -/
theorem c064_refutation_card :
    ¬ (∀ n : ℕ, 1 ≤ n → (rowA391736Values n).ncard = 1 + A115861 n) := by
  intro h
  have h239 := h 239 (by norm_num)
  have hgt := rowA391736_239_gt
  omega

/-- Pointwise refutation of the `n ^ 3` search-bound sufficiency conjecture:
there exist `n ≥ 1` and `1 ≤ m < n` occurring on row `n` of `A391736` with NO witness
`i ∈ {1, ..., n ^ 3}`. -/
theorem c064_refutation_pointwise :
    ¬ (∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, 1 ≤ m → m < n →
      m ∈ rowA391736Values n → ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ^ 3 ∧ m * i = clMul n i) := by
  intro h
  have hw := c064_witness
  have h215_in : 215 ∈ rowA391736Values 239 :=
    ⟨302775165, by norm_num, hw.2.2.2.1, hw.2.2.2.2.1⟩
  obtain ⟨i, hi1, hile, heq⟩ := h 239 (by norm_num) 215 hw.1 hw.2.1 h215_in
  exact hw.2.2.2.2.2 i hi1 hile heq

/-- General doubling monotonicity + strict increase lemma for `A115861`:
if `m ∈ A115861_set (2 * n)` is not twice any element of `A115861_set n`, then
`A115861 n < A115861 (2 * n)`. -/
lemma A115861_lt_double_of_new {n m : ℕ}
    (hm_in : m ∈ A115861_set (2 * n))
    (hm_not : m ∉ (A115861_set n).image (2 * ·)) :
    A115861 n < A115861 (2 * n) := by
  have hsub : (A115861_set n).image (2 * ·) ⊆ A115861_set (2 * n) := by
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [mem_A115861_set_iff] at hx ⊢
    rcases hx with ⟨⟨hx0, hx_lt⟩, ⟨i, hi1, hile, heq⟩⟩
    have hpow : n ^ 3 ≤ (2 * n) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    refine ⟨⟨by omega, by omega⟩, ⟨i, hi1, le_trans hile hpow, ?_⟩⟩
    rw [clMul_two_mul_left, ← heq]
    ring
  have hssub : (A115861_set n).image (2 * ·) ⊂ A115861_set (2 * n) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hm_not (heq.symm ▸ hm_in)⟩
  have hlt : ((A115861_set n).image (2 * ·)).card < (A115861_set (2 * n)).card :=
    Finset.card_lt_card hssub
  have hinj : Function.Injective (fun x : ℕ => 2 * x) := fun a b hab => by dsimp at hab; omega
  rw [Finset.card_image_of_injective _ hinj] at hlt
  exact hlt

/-- Corollary refuting `OEIS A115861` `%F` (`a(2 * n) = a(n)` for all `n ≥ 1`) under the
published `n ^ 3`-truncated definition: fails at `n = 478`, where `A115861(478) < A115861(956)`. -/
theorem c064_refutation_doubling :
    ¬ (∀ n : ℕ, 1 ≤ n → A115861 (2 * n) = A115861 n) := by
  intro h
  have h478 : A115861 (2 * 478) = A115861 478 := h 478 (by norm_num)
  have h860_in : 860 ∈ A115861_set (2 * 478) := by
    rw [mem_A115861_set_iff]
    refine ⟨⟨by norm_num, by norm_num⟩, ⟨302775165, by norm_num, by norm_num, ?_⟩⟩
    have h478_eq : (478 : ℕ) = 2 * 239 := by norm_num
    rw [h478_eq, clMul_two_mul_left, clMul_two_mul_left, clMul_239_302775165]
  have h860_not_in : 860 ∉ (A115861_set 478).image (2 * ·) := by
    rw [Finset.mem_image]
    rintro ⟨m, hm, h2m⟩
    rw [mem_A115861_set_iff] at hm
    rcases hm with ⟨_, ⟨i, hi1, hile, heq⟩⟩
    have hm430 : m = 430 := by omega
    subst hm430
    have h478_eq : (478 : ℕ) = 2 * 239 := by norm_num
    rw [h478_eq, clMul_two_mul_left] at heq
    have h215 : 215 * i = clMul 239 i := by omega
    exact no_sol_lt_2pow28 i hi1 (by omega) h215
  have hlt : A115861 478 < A115861 (2 * 478) := A115861_lt_double_of_new h860_in h860_not_in
  omega

/-! ### Section 6: Secondary Witness Product Identities (Beyond `n ^ 4` and `n ^ 5`) -/

def chain_391 : List (ℕ × ℕ) := [
  (1, 391), (2, 782), (5, 1947), (10, 3894),
  (21, 8171), (43, 15953), (86, 31906), (173, 63683),
  (346, 127366), (693, 254603), (1387, 509073), (2774, 1018146),
  (5548, 2036292), (11097, 4072719), (22194, 8145438), (44389, 16291259),
  (88779, 32582385), (177559, 65164389), (355119, 130328909), (710239, 260657949),
  (1420479, 521316285), (2840959, 1042632445), (5681919, 2085264509), (11363838, 4170529018),
  (22727677, 8341057651), (45455354, 16682115302), (90910709, 33364230219), (181821418, 66728460438),
  (363642836, 133456920876), (727285673, 266913842143), (1454571346, 533827684286), (2909142693, 1067655368443),
  (5818285386, 2135310736886), (11636570772, 4270621473772), (23273141545, 8541242947167), (46546283091, 17082485894457),
  (93092566182, 34164971788914), (186185132365, 68329943577955)
]

def chain_511 : List (ℕ × ℕ) := [
  (1, 511), (2, 1022), (4, 2044), (8, 4088),
  (16, 8176), (32, 16352), (64, 32704), (128, 65408),
  (257, 130815), (515, 261121), (1030, 522242), (2060, 1044484),
  (4121, 2089463), (8242, 4178926), (16484, 8357852), (32969, 16715335),
  (65938, 33430670), (131876, 66861340), (263752, 133722680), (527505, 267445647),
  (1055011, 534891233), (2110023, 1069782077), (4220047, 2139564421), (8440095, 4279128821),
  (16880191, 8558257173), (33760383, 17116514773), (67520767, 34233029205), (135041534, 68466058410),
  (270083069, 136932116651), (540166139, 273864233129), (1080332279, 547728466093), (2160664559, 1095456932005),
  (4321329119, 2190913863861), (8642658239, 4381827727509), (17285316479, 8763655454933), (34570632958, 17527310909866),
  (69141265916, 35054621819732), (138282531833, 70109243639639), (276565063667, 140218487279441), (553130127334, 280436974558882),
  (1106260254669, 560873949117627), (2212520509339, 1121747898235017), (4425041018678, 2243495796470034), (8850082037357, 4486991592940507),
  (17700164074715, 8973983185880649), (35400328149431, 17947966371761517)
]

/-- Secondary witness exceeding `n ^ 4`: `(n = 391, m = 367, i = 186185132365 > 391 ^ 4)`. -/
theorem c064_secondary_n4 :
    391 ^ 4 < 186185132365 ∧ 186185132365 % 2 = 1 ∧
    367 * 186185132365 = clMul 391 186185132365 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have h : clMul 391 186185132365 = 68329943577955 :=
    clMul_of_chain (by norm_num) chain_391 rfl (by simp [chain_391])
  rw [h]

/-- Secondary witness exceeding `n ^ 5`: `(n = 511, m = 507, i = 35400328149431 > 511 ^ 5)`. -/
theorem c064_secondary_n5 :
    511 ^ 5 < 35400328149431 ∧ 35400328149431 % 2 = 1 ∧
    507 * 35400328149431 = clMul 511 35400328149431 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have h : clMul 511 35400328149431 = 17947966371761517 :=
    clMul_of_chain (by norm_num) chain_511 rfl (by simp [chain_511])
  rw [h]

end C064
