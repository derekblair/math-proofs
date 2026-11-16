import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Seam C Entry S006 (OEIS A363166): Gómez Calderón's 3-Heap Nim Identity

Formalizes and proves Alan Michael Gómez Calderón's conjectured formula on `OEIS A363166`
(`%F` line 17, Sep 18 2025; live revision `#26`, Sep 23 2025) and companion `OEIS A063915`
(`%F` lines 17–18, Kevin Ryde, Nov 27 2020) against the frozen target contract `PIN-S006.md` v1
(`delta_vs_source: NONE`), following the 6-step MSB row-slice bijection route from
`SCOPING-S006.md` (§2.2, Steps 1–6).
-/

namespace SeamC.A363166

open scoped BigOperators

/-! ### Pinned Target Definitions (`PIN-S006.md` v1) -/

/-- `OEIS A363166(n)` (for `n ≥ 1`): cardinality of the finite set of unordered nonzero heap
triples `((x, y), z)` in `((Finset.Icc 1 n ×ˢ Finset.Icc 1 n) ×ˢ Finset.Icc 1 n)` satisfying
`x ≤ y ∧ y ≤ z ∧ Nat.xor (Nat.xor x y) z = 0` (`nimTriples 1 = 0`). -/
def nimTriples (n : ℕ) : ℕ :=
  (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n) ×ˢ Finset.Icc 1 n).filter
    (fun ((x, y), z) => x ≤ y ∧ y ≤ z ∧ Nat.xor (Nat.xor x y) z = 0)).card

/-- Auxiliary binary recurrence `b(n)` from `OEIS A063915` (`%F` line 17, `%t` lines 23–25):
`a063915Aux 0 = 0`, `a063915Aux 1 = 1`, `a063915Aux (2 * k) = 2 * a063915Aux k +
2 * a063915Aux (k - 1) + 1` for `k ≥ 1`, and `a063915Aux (2 * k + 1) = 4 * a063915Aux k + 1`
for `k ≥ 1`. -/
def a063915Aux : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then
      2 * a063915Aux ((n + 2) / 2) + 2 * a063915Aux ((n + 2) / 2 - 1) + 1
    else
      4 * a063915Aux ((n + 2) / 2) + 1

/-- `OEIS A063915(m)`: `a063915 m = a063915Aux (m + 1)` (`a063915 0 = 1`, `a063915 1 = 3`,
`a063915 2 = 5`). -/
def a063915 (m : ℕ) : ℕ :=
  a063915Aux (m + 1)

/-! ### Step 1: Bitwise XOR Cancellation & Strict Heap Inequalities (`SCOPING-S006.md` §2.2 Step 1) -/

private theorem nat_xor_eq_hxor (a b : ℕ) : Nat.xor a b = a ^^^ b :=
  rfl

@[simp]
theorem testBit_natXor (a b i : ℕ) :
    (Nat.xor a b).testBit i = bne (a.testBit i) (b.testBit i) := by
  rw [nat_xor_eq_hxor, Nat.testBit_xor]

theorem xor_eq_zero_iff_eq (a b : ℕ) : Nat.xor a b = 0 ↔ a = b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have hi := congrArg (fun n => Nat.testBit n i) h
    simp only [testBit_natXor, Nat.zero_testBit] at hi
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  · rintro rfl
    apply Nat.eq_of_testBit_eq
    intro i
    simp

theorem xor_triple_eq_zero_iff (x y z : ℕ) :
    Nat.xor (Nat.xor x y) z = 0 ↔ z = Nat.xor x y :=
  (xor_eq_zero_iff_eq (Nat.xor x y) z).trans eq_comm

theorem eq_xor_of_xor_triple_eq_zero {x y z : ℕ} (h : Nat.xor (Nat.xor x y) z = 0) :
    x = Nat.xor y z := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun n => Nat.testBit n i) h
  simp only [testBit_natXor, Nat.zero_testBit] at hi ⊢
  cases hx : x.testBit i <;> cases hy : y.testBit i <;> cases hz : z.testBit i <;> simp_all

theorem xor_cancel_triple (y z : ℕ) : Nat.xor (Nat.xor (Nat.xor y z) y) z = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_natXor, Nat.zero_testBit]
  cases y.testBit i <;> cases z.testBit i <;> rfl

/-- Step 1 (`SCOPING-S006.md` §2.2): every nonzero zero-XOR sorted triple `1 ≤ x ≤ y ≤ z`
automatically satisfies strict inequalities `1 ≤ x < y < z`, with `x = y ⊕ z` and `z = x ⊕ y`. -/
theorem strict_lt_of_xor_zero {x y z : ℕ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hxor : Nat.xor (Nat.xor x y) z = 0) :
    x < y ∧ y < z ∧ x = Nat.xor y z ∧ z = Nat.xor x y := by
  have hz_eq : z = Nat.xor x y := (xor_triple_eq_zero_iff x y z).mp hxor
  have hx_eq : x = Nat.xor y z := eq_xor_of_xor_triple_eq_zero hxor
  refine ⟨lt_of_le_of_ne hxy ?_, lt_of_le_of_ne hyz ?_, hx_eq, hz_eq⟩
  · intro heq
    subst heq
    have hz0 : z = 0 := by
      rw [hz_eq]
      exact (xor_eq_zero_iff_eq x x).mpr rfl
    omega
  · intro heq
    subst heq
    have hx0 : x = 0 := by
      rw [hx_eq]
      exact (xor_eq_zero_iff_eq y y).mpr rfl
    omega

/-! ### Step 2: Canonical Triangular Pair Model `𝒯_n` & Row Sums (`SCOPING-S006.md` §2.2 Step 2) -/

/-- Canonical triangular pair model `𝒯_n = {(y, z) ∈ [0, n] × [1, n] : y < z}`
(`OEIS A000217` `%C` line 23). -/
def triangularPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 0 n ×ˢ Finset.Icc 1 n).filter (fun p => p.1 < p.2)

private theorem Icc_one_succ (n : ℕ) :
    Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
  ext z
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

private theorem mul_succ_mod_two (n : ℕ) : n * (n + 1) % 2 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    rw [hstep]
    omega

theorem sum_Icc_one_id (n : ℕ) : (∑ z ∈ Finset.Icc 1 n, z) = n * (n + 1) / 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Icc_one_succ, Finset.sum_insert (by simp), ih]
    have hmod := mul_succ_mod_two n
    have hstep : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    rw [hstep]
    omega

theorem card_triangularPairs (n : ℕ) : (triangularPairs n).card = n * (n + 1) / 2 := by
  suffices hsum : (triangularPairs n).card = ∑ z ∈ Finset.Icc 1 n, z by
    rw [hsum, sum_Icc_one_id]
  induction n with
  | zero => rfl
  | succ n ih =>
    let rowSet : Finset (ℕ × ℕ) := (Finset.range (n + 1)).image (fun y => (y, n + 1))
    have hpart : triangularPairs (n + 1) = triangularPairs n ∪ rowSet := by
      ext ⟨y, z⟩
      simp only [triangularPairs, rowSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
      constructor
      · intro h
        by_cases hz : z ≤ n
        · left; omega
        · right; exact ⟨y, by omega, ⟨rfl, by omega⟩⟩
      · rintro (h | ⟨y', hy', ⟨rfl, rfl⟩⟩) <;> omega
    have hdisj : Disjoint (triangularPairs n) rowSet := by
      rw [Finset.disjoint_left]
      rintro ⟨y, z⟩ h1 h2
      simp only [triangularPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h1
      simp only [rowSet, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at h2
      rcases h2 with ⟨_, _, ⟨_, rfl⟩⟩
      omega
    have hcard_row : rowSet.card = n + 1 := by
      dsimp only [rowSet]
      rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), Finset.card_range]
    rw [hpart, Finset.card_union_of_disjoint hdisj, ih, hcard_row,
      Icc_one_succ, Finset.sum_insert (by simp), add_comm]

/-! ### Step 3: Core Lemma — MSB Row-Slice Bijection `msb_xor_slice_bij` (`SCOPING-S006.md` §2.2 Step 3) -/

/-- Every integer `n ∈ [2^r, 2^(r+1))` has bit `r` equal to `true`. -/
theorem testBit_eq_true_of_mem_dyadic {n r : ℕ} (hlo : 2 ^ r ≤ n) (hhi : n < 2 ^ (r + 1)) :
    n.testBit r = true := by
  have hp : 0 < 2 ^ r := Nat.two_pow_pos r
  have hhi' : n < 2 * 2 ^ r := by
    rw [Nat.pow_add, Nat.pow_one] at hhi
    omega
  have hge1 : 1 ≤ n / 2 ^ r := (Nat.le_div_iff_mul_le hp).mpr (by omega)
  have hlt2 : n / 2 ^ r < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  have hdiv : n / 2 ^ r = 1 := by omega
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]

/-- If every bit `j ≥ r` of `x` is `false`, then `x < 2^r`. -/
theorem lt_two_pow_of_testBit_false {x r : ℕ}
    (h : ∀ j : ℕ, r ≤ j → x.testBit j = false) : x < 2 ^ r := by
  by_contra hge
  have hle : 2 ^ r ≤ x := Nat.le_of_not_gt hge
  have hx0 : x ≠ 0 := by
    have hp := Nat.two_pow_pos r
    omega
  set k := Nat.log 2 x
  have hrk : r ≤ k := Nat.le_log_of_pow_le Nat.one_lt_two hle
  have hk_lo : 2 ^ k ≤ x := Nat.pow_log_le_self 2 hx0
  have hk_hi : x < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two x
  have ht : x.testBit k = true := testBit_eq_true_of_mem_dyadic hk_lo hk_hi
  have hf : x.testBit k = false := h k hrk
  rw [ht] at hf
  exact Bool.noConfusion hf

/-- Forward bitwise bound of Step 3: if `2^(Nat.log 2 z) ≤ y < z`, then `y` and `z` share MSB
index `r = Nat.log 2 z`, cancelling bit `r` in `y ⊕ z` so that `Nat.xor y z < 2^(Nat.log 2 z)`. -/
theorem xor_lt_two_pow_log {y z : ℕ} (hz : 1 ≤ z)
    (hy_lo : 2 ^ Nat.log 2 z ≤ y) (hy_hi : y < z) :
    Nat.xor y z < 2 ^ Nat.log 2 z := by
  set r := Nat.log 2 z
  have hz0 : z ≠ 0 := by omega
  have hz_lo : 2 ^ r ≤ z := Nat.pow_log_le_self 2 hz0
  have hz_hi : z < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two z
  have hy_hi' : y < 2 ^ (r + 1) := lt_trans hy_hi hz_hi
  apply lt_two_pow_of_testBit_false
  intro j hrj
  rw [testBit_natXor]
  rcases eq_or_lt_of_le hrj with rfl | hlt
  · rw [testBit_eq_true_of_mem_dyadic hy_lo hy_hi', testBit_eq_true_of_mem_dyadic hz_lo hz_hi]
    rfl
  · have hpow : 2 ^ (r + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy_hi' hpow),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz_hi hpow)]
    rfl

/-- Inverse bitwise bound of Step 3: any valid triple `1 ≤ x ≤ y ≤ z` with `(x ⊕ y) ⊕ z = 0` must
have `2^(Nat.log 2 z) ≤ y` (otherwise `x ≤ y < 2^r` would force bit `r` of `z = x ⊕ y` to be `0`). -/
theorem two_pow_log_le_of_xor_zero {x y z : ℕ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hxor : Nat.xor (Nat.xor x y) z = 0) :
    2 ^ Nat.log 2 z ≤ y := by
  set r := Nat.log 2 z
  by_contra hlt
  have hy_lt : y < 2 ^ r := Nat.lt_of_not_ge hlt
  have hx_lt : x < 2 ^ r := lt_of_le_of_lt hxy hy_lt
  have hz_eq : z = Nat.xor x y := (xor_triple_eq_zero_iff x y z).mp hxor
  have hz_false : z.testBit r = false := by
    rw [hz_eq, testBit_natXor, Nat.testBit_eq_false_of_lt hx_lt, Nat.testBit_eq_false_of_lt hy_lt]
    rfl
  have hz0 : z ≠ 0 := by omega
  have hz_true : z.testBit r = true :=
    testBit_eq_true_of_mem_dyadic (Nat.pow_log_le_self 2 hz0)
      (Nat.lt_pow_succ_log_self Nat.one_lt_two z)
  rw [hz_true] at hz_false
  exact Bool.noConfusion hz_false

/-- The `z`-maximal fiber `𝒫_z` of valid unordered nonzero Nim triples with largest heap `z`. -/
def maxFiber (z : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((Finset.Icc 1 z ×ˢ Finset.Icc 1 z) ×ˢ ({z} : Finset ℕ)).filter
    (fun ((x, y), z') => x ≤ y ∧ y ≤ z' ∧ Nat.xor (Nat.xor x y) z' = 0))

theorem mem_maxFiber {x y z' z : ℕ} :
    ((x, y), z') ∈ maxFiber z ↔
      1 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ z' = z ∧ Nat.xor (Nat.xor x y) z = 0 := by
  simp only [maxFiber, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨⟨hx1, _⟩, ⟨_, _⟩⟩, hz_eq⟩, hxy, hyz, hxor⟩
    subst hz_eq
    exact ⟨hx1, hxy, hyz, rfl, hxor⟩
  · rintro ⟨hx1, hxy, hyz, hz_eq, hxor⟩
    subst hz_eq
    exact ⟨⟨⟨⟨hx1, by omega⟩, ⟨by omega, hyz⟩⟩, rfl⟩, hxy, hyz, hxor⟩

/-- Core lemma (`SCOPING-S006.md` §2.2 Step 3 & §5.2): for every `z ≥ 1` with `r = Nat.log 2 z`,
`y ↦ ((Nat.xor y z, y), z)` is a bijection from `Finset.Ico (2 ^ r) z` onto `maxFiber z`, so
`(maxFiber z).card = z - 2 ^ Nat.log 2 z`. -/
theorem msb_xor_slice_bij {z : ℕ} (hz : 1 ≤ z) :
    (maxFiber z).card = z - 2 ^ Nat.log 2 z := by
  symm
  rw [← Nat.card_Ico]
  refine Finset.card_bij (fun y _ => ((Nat.xor y z, y), z)) ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_Ico] at hy
    rw [mem_maxFiber]
    have hx_lt : Nat.xor y z < 2 ^ Nat.log 2 z := xor_lt_two_pow_log hz hy.1 hy.2
    have hx_ne : Nat.xor y z ≠ 0 := by
      intro h0
      exact (ne_of_lt hy.2) ((xor_eq_zero_iff_eq y z).mp h0)
    refine ⟨by omega, by omega, by omega, rfl, xor_cancel_triple y z⟩
  · intro y₁ _ y₂ _ heq
    exact (Prod.mk.inj (Prod.mk.inj heq).1).2
  · rintro ⟨⟨x, y⟩, z'⟩ ht
    rw [mem_maxFiber] at ht
    rcases ht with ⟨hx1, hxy, hyz, hz_eq, hxor⟩
    subst z'
    obtain ⟨_, hy_lt_z, hx_eq, _⟩ := strict_lt_of_xor_zero hx1 hxy hyz hxor
    have hy_lo : 2 ^ Nat.log 2 z ≤ y := two_pow_log_le_of_xor_zero hx1 hxy hyz hxor
    refine ⟨y, Finset.mem_Ico.mpr ⟨hy_lo, hy_lt_z⟩, ?_⟩
    rw [← hx_eq]

/-! ### Step 4: Row-Sum Partition `nimTriples n + msbSum n = n * (n + 1) / 2` -/

private def nimTripleSet (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n) ×ˢ Finset.Icc 1 n).filter
    (fun ((x, y), z) => x ≤ y ∧ y ≤ z ∧ Nat.xor (Nat.xor x y) z = 0))

private theorem mem_nimTripleSet {x y z n : ℕ} :
    ((x, y), z) ∈ nimTripleSet n ↔
      1 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ z ≤ n ∧ Nat.xor (Nat.xor x y) z = 0 := by
  simp only [nimTripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨⟨hx1, _⟩, ⟨_, _⟩⟩, ⟨_, hzn⟩⟩, hxy, hyz, hxor⟩
    exact ⟨hx1, hxy, hyz, hzn, hxor⟩
  · rintro ⟨hx1, hxy, hyz, hzn, hxor⟩
    exact ⟨⟨⟨⟨hx1, by omega⟩, ⟨by omega, by omega⟩⟩, ⟨by omega, hzn⟩⟩, hxy, hyz, hxor⟩

/-- Step recurrence for `nimTriples`: incrementing the cap from `n` to `n + 1` adds
`(n + 1) - 2^(Nat.log 2 (n + 1))` (`OEIS A053645(n + 1)`) P-positions. -/
theorem nimTriples_succ (n : ℕ) :
    nimTriples (n + 1) = nimTriples n + (n + 1 - 2 ^ Nat.log 2 (n + 1)) := by
  change (nimTripleSet (n + 1)).card =
    (nimTripleSet n).card + (n + 1 - 2 ^ Nat.log 2 (n + 1))
  have hpart : nimTripleSet (n + 1) = nimTripleSet n ∪ maxFiber (n + 1) := by
    ext ⟨⟨x, y⟩, z⟩
    rw [Finset.mem_union, mem_nimTripleSet, mem_nimTripleSet, mem_maxFiber]
    constructor
    · rintro ⟨hx1, hxy, hyz, hzn, hxor⟩
      by_cases hz : z ≤ n
      · exact Or.inl ⟨hx1, hxy, hyz, hz, hxor⟩
      · have hzeq : z = n + 1 := by omega
        subst hzeq
        exact Or.inr ⟨hx1, hxy, hyz, rfl, hxor⟩
    · rintro (⟨hx1, hxy, hyz, hzn, hxor⟩ | ⟨hx1, hxy, hyz, hz_eq, hxor⟩)
      · exact ⟨hx1, hxy, hyz, by omega, hxor⟩
      · subst hz_eq
        exact ⟨hx1, hxy, hyz, le_rfl, hxor⟩
  have hdisj : Disjoint (nimTripleSet n) (maxFiber (n + 1)) := by
    rw [Finset.disjoint_left]
    rintro ⟨⟨x, y⟩, z⟩ h1 h2
    rw [mem_nimTripleSet] at h1
    rw [mem_maxFiber] at h2
    omega
  rw [hpart, Finset.card_union_of_disjoint hdisj, msb_xor_slice_bij (by omega : 1 ≤ n + 1)]

theorem nimTriples_eq_sum (n : ℕ) :
    nimTriples n = ∑ z ∈ Finset.Icc 1 n, (z - 2 ^ Nat.log 2 z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nimTriples_succ, ih, Icc_one_succ, Finset.sum_insert (by simp), add_comm]

/-- MSB partial sum `B(n) = ∑_{z=1}^n 2^(Nat.log 2 z)` (`SCOPING-S006.md` §2.2 Steps 4–5). -/
def msbSum (n : ℕ) : ℕ :=
  ∑ z ∈ Finset.Icc 1 n, 2 ^ Nat.log 2 z

theorem msbSum_succ (n : ℕ) :
    msbSum (n + 1) = msbSum n + 2 ^ Nat.log 2 (n + 1) := by
  unfold msbSum
  rw [Icc_one_succ, Finset.sum_insert (by simp), add_comm]

/-- Step 4 (`SCOPING-S006.md` §2.2): `nimTriples n + msbSum n = n * (n + 1) / 2`. -/
theorem nimTriples_add_msbSum_eq_triangular (n : ℕ) :
    nimTriples n + msbSum n = n * (n + 1) / 2 := by
  rw [← sum_Icc_one_id]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nimTriples_succ, msbSum_succ, Icc_one_succ, Finset.sum_insert (by simp)]
    have hle : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
    omega

/-! ### Step 5: Equivalence `a063915Aux n = msbSum n` (`SCOPING-S006.md` §2.2 Step 5) -/

private theorem two_pow_log_two_mul {j : ℕ} (hj : 1 ≤ j) :
    2 ^ Nat.log 2 (2 * j) = 2 * 2 ^ Nat.log 2 j := by
  have hge : 2 ≤ 2 * j := by omega
  have hdiv : (2 * j) / 2 = j := by omega
  rw [Nat.log_of_one_lt_of_le Nat.one_lt_two hge, hdiv, Nat.pow_add, Nat.pow_one]
  ring

private theorem two_pow_log_two_mul_add_one {j : ℕ} (hj : 1 ≤ j) :
    2 ^ Nat.log 2 (2 * j + 1) = 2 * 2 ^ Nat.log 2 j := by
  have hge : 2 ≤ 2 * j + 1 := by omega
  have hdiv : (2 * j + 1) / 2 = j := by omega
  rw [Nat.log_of_one_lt_of_le Nat.one_lt_two hge, hdiv, Nat.pow_add, Nat.pow_one]
  ring

theorem msbSum_two_mul_add_one (k : ℕ) :
    msbSum (2 * k + 1) = 4 * msbSum k + 1 := by
  induction k with
  | zero =>
    simp [msbSum]
  | succ k ih =>
    have h1 : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
    rw [h1, msbSum_succ, msbSum_succ, ih,
      show (2 * k + 1) + 1 = 2 * (k + 1) by omega,
      two_pow_log_two_mul (by omega : 1 ≤ k + 1),
      two_pow_log_two_mul_add_one (by omega : 1 ≤ k + 1),
      msbSum_succ]
    ring

theorem msbSum_two_mul {k : ℕ} (hk : 1 ≤ k) :
    msbSum (2 * k) = 2 * msbSum k + 2 * msbSum (k - 1) + 1 := by
  have hodd : msbSum (2 * k + 1) = msbSum (2 * k) + 2 ^ Nat.log 2 (2 * k + 1) :=
    msbSum_succ (2 * k)
  rw [msbSum_two_mul_add_one k, two_pow_log_two_mul_add_one hk] at hodd
  have hk_step : msbSum k = msbSum (k - 1) + 2 ^ Nat.log 2 k := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [msbSum_succ, show (k - 1) + 1 = k by omega]
  omega

/-- Explicit verification of the `%F` line 17 equations for `a063915Aux`. -/
theorem a063915Aux_two_mul {k : ℕ} (hk : 1 ≤ k) :
    a063915Aux (2 * k) = 2 * a063915Aux k + 2 * a063915Aux (k - 1) + 1 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 2 := ⟨2 * k - 2, by omega⟩
  rw [hm, a063915Aux]
  have heven : (m + 2) % 2 = 0 := by omega
  have hdiv : (m + 2) / 2 = k := by omega
  simp only [heven, ↓reduceIte, hdiv]

theorem a063915Aux_two_mul_add_one {k : ℕ} (hk : 1 ≤ k) :
    a063915Aux (2 * k + 1) = 4 * a063915Aux k + 1 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * k + 1 = m + 2 := ⟨2 * k - 1, by omega⟩
  rw [hm, a063915Aux]
  have hodd : ¬ (m + 2) % 2 = 0 := by omega
  have hdiv : (m + 2) / 2 = k := by omega
  simp only [hodd, ↓reduceIte, hdiv]

/-- Step 5 (`SCOPING-S006.md` §2.2): `a063915Aux n = msbSum n` for every `n : ℕ`. -/
theorem a063915Aux_eq_msbSum (n : ℕ) : a063915Aux n = msbSum n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [a063915Aux, msbSum]
    | 1 => simp [a063915Aux, msbSum]
    | m + 2 =>
      by_cases heven : (m + 2) % 2 = 0
      · set k := (m + 2) / 2
        have hk1 : 1 ≤ k := by omega
        have hmk : m + 2 = 2 * k := by omega
        rw [hmk, a063915Aux_two_mul hk1, ih k (by omega), ih (k - 1) (by omega),
          ← msbSum_two_mul hk1]
      · set k := (m + 2) / 2
        have hk1 : 1 ≤ k := by omega
        have hmk : m + 2 = 2 * k + 1 := by omega
        rw [hmk, a063915Aux_two_mul_add_one hk1, ih k (by omega), ← msbSum_two_mul_add_one k]

/-! ### Step 6: Kevin Ryde Closed Form & Exact Division by 3 (`SCOPING-S006.md` §2.2 Step 6) -/

theorem three_dvd_two_mul_four_pow_add_one (k : ℕ) : 3 ∣ 2 * 4 ^ k + 1 := by
  induction k with
  | zero => exact ⟨1, rfl⟩
  | succ k ih =>
    rcases ih with ⟨q, hq⟩
    refine ⟨q + 2 * 4 ^ k, ?_⟩
    rw [Nat.pow_add, Nat.pow_one]
    omega

/-- Step 6 (`SCOPING-S006.md` §2.2): `3 * msbSum n + (2 * 4^k + 1) = 3 * (n + 1) * 2^k`
for `k = Nat.log 2 (n + 1)`, proved by induction across the dyadic jump `n + 2 = 2^(k' + 1)`. -/
theorem three_mul_msbSum_closed_form (n : ℕ) :
    let k := Nat.log 2 (n + 1)
    3 * msbSum n + (2 * 4 ^ k + 1) = 3 * (n + 1) * 2 ^ k := by
  change 3 * msbSum n + (2 * 4 ^ Nat.log 2 (n + 1) + 1) = 3 * (n + 1) * 2 ^ Nat.log 2 (n + 1)
  induction n with
  | zero => simp [msbSum]
  | succ n ih =>
    set k' := Nat.log 2 (n + 1) with hk'_def
    set k := Nat.log 2 (n + 2) with hk_def
    have hstep : 3 * msbSum (n + 1) + (2 * 4 ^ k' + 1) = 3 * (n + 2) * 2 ^ k' := by
      calc
        3 * msbSum (n + 1) + (2 * 4 ^ k' + 1)
          = (3 * msbSum n + (2 * 4 ^ k' + 1)) + 3 * 2 ^ k' := by
            rw [msbSum_succ, ← hk'_def]; ring
        _ = 3 * (n + 1) * 2 ^ k' + 3 * 2 ^ k' := by rw [ih]
        _ = 3 * (n + 2) * 2 ^ k' := by ring
    have hk'_lo : 2 ^ k' ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
    have hk'_hi : n + 1 < 2 ^ (k' + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two (n + 1)
    rcases Nat.lt_or_eq_of_le (show n + 2 ≤ 2 ^ (k' + 1) by omega) with hlt | heq
    · have hk_eq : k = k' :=
        Nat.log_eq_of_pow_le_of_lt_pow (by omega : 2 ^ k' ≤ n + 2) hlt
      rwa [hk_eq]
    · have hk_eq : k = k' + 1 := by
        rw [hk_def, heq, Nat.log_pow Nat.one_lt_two]
      have hpow2 : 2 ^ (k' + 1) = 2 * 2 ^ k' := by
        rw [Nat.pow_add, Nat.pow_one]; ring
      have hpow4_succ : 4 ^ (k' + 1) = 4 * 4 ^ k' := by
        rw [Nat.pow_add, Nat.pow_one]; ring
      have hpow4_sq : 4 ^ k' = 2 ^ k' * 2 ^ k' := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, Nat.mul_pow]
      rw [hk_eq, heq, hpow2, hpow4_succ, hpow4_sq]
      rw [heq, hpow2, hpow4_sq] at hstep
      set p := 2 ^ k'
      have h6 : 3 * (2 * p) * p = 6 * (p * p) := by ring
      have h12 : 3 * (2 * p) * (2 * p) = 12 * (p * p) := by ring
      omega

/-! ### Pinned Target Theorems (`PIN-S006.md` v1) -/

/-- Primary theorem (`OEIS A363166` `%F` line 17, Alan Michael Gómez Calderón, Sep 18 2025):
for every `n : ℕ` with `1 ≤ n`, `nimTriples n + a063915 (n - 1) = n * (n + 1) / 2`. -/
theorem nim_triples_add_a063915_eq_triangular (n : ℕ) (hn : 1 ≤ n) :
    nimTriples n + a063915 (n - 1) = n * (n + 1) / 2 := by
  unfold a063915
  rw [show n - 1 + 1 = n by omega, a063915Aux_eq_msbSum, nimTriples_add_msbSum_eq_triangular]

/-- Companion equivalence theorem (`OEIS A063915` `%F` line 18, Kevin Ryde, Nov 27 2020):
for every `m : ℕ`, letting `k = Nat.log 2 (m + 2)`,
`3 * a063915 m + (2 * 4 ^ k + 1) = 3 * (m + 2) * 2 ^ k` and
`a063915 m = (m + 2) * 2 ^ k - (2 * 4 ^ k + 1) / 3`. -/
theorem a063915_eq_closed_form (m : ℕ) :
    let k := Nat.log 2 (m + 2)
    3 * a063915 m + (2 * 4 ^ k + 1) = 3 * (m + 2) * 2 ^ k ∧
      a063915 m = (m + 2) * 2 ^ k - (2 * 4 ^ k + 1) / 3 := by
  set k := Nat.log 2 (m + 2)
  have ha : a063915 m = msbSum (m + 1) := by
    unfold a063915
    exact a063915Aux_eq_msbSum (m + 1)
  have h3 : 3 * a063915 m + (2 * 4 ^ k + 1) = 3 * (m + 2) * 2 ^ k := by
    rw [ha]
    exact three_mul_msbSum_closed_form (m + 1)
  refine ⟨h3, ?_⟩
  rcases three_dvd_two_mul_four_pow_add_one k with ⟨q, hq⟩
  have h3' : 3 * a063915 m + 3 * q = 3 * ((m + 2) * 2 ^ k) := by
    calc
      3 * a063915 m + 3 * q = 3 * a063915 m + (2 * 4 ^ k + 1) := by rw [hq]
      _ = 3 * (m + 2) * 2 ^ k := h3
      _ = 3 * ((m + 2) * 2 ^ k) := by ring
  change a063915 m = (m + 2) * 2 ^ k - (2 * 4 ^ k + 1) / 3
  rw [hq]
  omega

/-- Closed-form corollary: for every `n : ℕ` with `1 ≤ n`, letting `k = Nat.log 2 (n + 1)`,
`nimTriples n + ((n + 1) * 2 ^ k - (2 * 4 ^ k + 1) / 3) = n * (n + 1) / 2`. -/
theorem nim_triples_add_closed_form_eq_triangular (n : ℕ) (hn : 1 ≤ n) :
    let k := Nat.log 2 (n + 1)
    nimTriples n + ((n + 1) * 2 ^ k - (2 * 4 ^ k + 1) / 3) = n * (n + 1) / 2 := by
  have hmain := nim_triples_add_a063915_eq_triangular n hn
  have hcf : a063915 (n - 1) =
      (n - 1 + 2) * 2 ^ Nat.log 2 (n - 1 + 2) - (2 * 4 ^ Nat.log 2 (n - 1 + 2) + 1) / 3 :=
    (a063915_eq_closed_form (n - 1)).2
  rw [show n - 1 + 2 = n + 1 by omega] at hcf
  change nimTriples n +
      ((n + 1) * 2 ^ Nat.log 2 (n + 1) - (2 * 4 ^ Nat.log 2 (n + 1) + 1) / 3) =
    n * (n + 1) / 2
  rwa [hcf] at hmain

/-! ### Classical Corollaries & Kernel Non-Vacuity Verification -/

private theorem one_add_sum_range_two_pow (r : ℕ) :
    1 + (∑ i ∈ Finset.range r, 2 ^ i) = 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, Nat.pow_add, Nat.pow_one]
    omega

/-- Coefficient-level `%N` line 10 OGF identity (`SCOPING-S006.md` §2.2 Step 6):
multiplying `1 + ∑_{i ≥ 0} 2^i x^(2^(i+1) - 1)` twice by `(1 - x)⁻¹` yields `[x^m] = a063915 m`
for every `m : ℕ`. -/
theorem a063915_eq_ogf_coeff (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
      (1 + ∑ i ∈ (Finset.range (j + 1)).filter (fun i => 2 ^ (i + 1) - 1 ≤ j), 2 ^ i)) =
      a063915 m := by
  have hinner : ∀ j : ℕ,
      1 + (∑ i ∈ (Finset.range (j + 1)).filter (fun i => 2 ^ (i + 1) - 1 ≤ j), 2 ^ i) =
        2 ^ Nat.log 2 (j + 1) := by
    intro j
    have hflt : (Finset.range (j + 1)).filter (fun i => 2 ^ (i + 1) - 1 ≤ j) =
        Finset.range (Nat.log 2 (j + 1)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      have hp : 1 ≤ 2 ^ (i + 1) := Nat.two_pow_pos (i + 1)
      have hlog_lt : Nat.log 2 (j + 1) < j + 1 := Nat.log_lt_self 2 (by omega)
      have hiff : i + 1 ≤ Nat.log 2 (j + 1) ↔ 2 ^ (i + 1) ≤ j + 1 :=
        Nat.le_log_iff_pow_le Nat.one_lt_two (by omega)
      omega
    rw [hflt, one_add_sum_range_two_pow]
  have hsum : ∀ n : ℕ,
      (∑ j ∈ Finset.range n,
        (1 + ∑ i ∈ (Finset.range (j + 1)).filter (fun i => 2 ^ (i + 1) - 1 ≤ j), 2 ^ i)) =
        msbSum n := by
    intro n
    induction n with
    | zero => simp [msbSum]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hinner n, msbSum_succ]
  rw [hsum (m + 1)]
  unfold a063915
  exact (a063915Aux_eq_msbSum (m + 1)).symm

/-- Kernel-verified refutation of the intake's `x ⊕ y > n` sketch (`SCOPING-S006.md` §2.1):
at the Mersenne cap `n = 3`, `#{1 ≤ x ≤ y ≤ 3 : x ⊕ y > 3} = 0 ≠ 5 = a063915 (3 - 1)`. -/
theorem refute_intake_xor_gt_sketch :
    (((Finset.Icc 1 3 ×ˢ Finset.Icc 1 3).filter
      (fun (x, y) => x ≤ y ∧ 3 < Nat.xor x y)).card = 0) ∧
    a063915 (3 - 1) = 5 := by
  refine ⟨rfl, ?_⟩
  simp [a063915, a063915Aux]

/-- Exact power-of-two flat-step property (`SCOPING-S006.md` §2.3): for every `m ≥ 1`,
`nimTriples (2 ^ m) = nimTriples (2 ^ m - 1)` because the upper slice `[2^m, 2^m)` is empty. -/
theorem nimTriples_two_pow_eq_pred (m : ℕ) (_hm : 1 ≤ m) :
    nimTriples (2 ^ m) = nimTriples (2 ^ m - 1) := by
  have hp : 1 ≤ 2 ^ m := Nat.two_pow_pos m
  conv_lhs => rw [show 2 ^ m = (2 ^ m - 1) + 1 by omega]
  rw [nimTriples_succ, show (2 ^ m - 1) + 1 = 2 ^ m by omega, Nat.log_pow Nat.one_lt_two]
  omega

/-- Bouton's 1901 dyadic-cap special case (`Ann. of Math.` 3, 1901, §3, p. 37; `OEIS A006095(m)`):
`6 * nimTriples (2^m - 1) = (2^m - 1) * (2^m - 2)` for every `m ≥ 1`. -/
theorem nimTriples_mersenne_eq_bouton (m : ℕ) (hm : 1 ≤ m) :
    6 * nimTriples (2 ^ m - 1) = (2 ^ m - 1) * (2 ^ m - 2) := by
  have hp2 : 2 ≤ 2 ^ m := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hm
    simpa using this
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ m = r + 2 := ⟨2 ^ m - 2, by omega⟩
  have hmain := nim_triples_add_a063915_eq_triangular (r + 1) (by omega)
  have h3 : 3 * a063915 r + (2 * 4 ^ Nat.log 2 (r + 2) + 1) =
      3 * (r + 2) * 2 ^ Nat.log 2 (r + 2) :=
    (a063915_eq_closed_form r).1
  have hlog : Nat.log 2 (r + 2) = m := by
    rw [← hr, Nat.log_pow Nat.one_lt_two]
  have hpow4 : 4 ^ m = (r + 2) * (r + 2) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, Nat.mul_pow, hr]
  rw [hlog, hr, hpow4] at h3
  have h3' : 3 * a063915 r + (2 * ((r + 2) * (r + 2)) + 1) = 3 * ((r + 2) * (r + 2)) := by
    calc
      3 * a063915 r + (2 * ((r + 2) * (r + 2)) + 1) = 3 * (r + 2) * (r + 2) := h3
      _ = 3 * ((r + 2) * (r + 2)) := by ring
  rw [show r + 1 - 1 = r by omega] at hmain
  have hmod := mul_succ_mod_two (r + 1)
  have hid : 3 * ((r + 1) * (r + 1 + 1)) + 2 = 2 * ((r + 2) * (r + 2)) + (r + 1) * r := by ring
  rw [hr, show r + 2 - 1 = r + 1 by omega, show r + 2 - 2 = r by omega]
  omega

/-- Pure `Nat`-structural-recursion mirror counting row `z`'s valid `y ∈ [1, m]` (`1 ≤ y ⊕ z ≤ y`),
free of `Finset`/`Quot` proof terms so that kernel `rfl` verifies `n = 1..32` and `m = 1..6`
without hitting `Quot` recursion depth limits. Proved equal to `nimTriples` directly from
`strict_lt_of_xor_zero` and `maxFiber` (independently of `nim_triples_add_a063915_eq_triangular`). -/
def nimRowFast (z : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    nimRowFast z m +
      if 1 ≤ Nat.xor (m + 1) z ∧ Nat.xor (m + 1) z ≤ m + 1 then 1 else 0

def nimTriplesFast : ℕ → ℕ
  | 0 => 0
  | z + 1 => nimTriplesFast z + nimRowFast (z + 1) (z + 1)

private theorem nimRowFast_eq_card_filter (z m : ℕ) :
    nimRowFast z m =
      ((Finset.Icc 1 m).filter (fun y => 1 ≤ Nat.xor y z ∧ Nat.xor y z ≤ y)).card := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [nimRowFast, ih, Icc_one_succ, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl

private theorem nimRowFast_self_eq_maxFiber (z : ℕ) :
    nimRowFast z z = (maxFiber z).card := by
  rw [nimRowFast_eq_card_filter]
  refine Finset.card_bij (fun y _ => ((Nat.xor y z, y), z)) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hy
    rw [mem_maxFiber]
    exact ⟨hy.2.1, hy.2.2, hy.1.2, rfl, xor_cancel_triple y z⟩
  · intro y₁ _ y₂ _ heq
    exact (Prod.mk.inj (Prod.mk.inj heq).1).2
  · rintro ⟨⟨x, y⟩, z'⟩ ht
    rw [mem_maxFiber] at ht
    rcases ht with ⟨hx1, hxy, hyz, hz_eq, hxor⟩
    subst hz_eq
    obtain ⟨_, _, hx_eq, _⟩ := strict_lt_of_xor_zero hx1 hxy hyz hxor
    refine ⟨y, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      rw [← hx_eq]
      exact ⟨⟨by omega, hyz⟩, hx1, hxy⟩
    · rw [← hx_eq]

theorem nimTriplesFast_eq_nimTriples (n : ℕ) : nimTriplesFast n = nimTriples n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nimTriplesFast, ih, nimRowFast_self_eq_maxFiber, nimTriples_succ,
      msb_xor_slice_bij (by omega : 1 ≤ n + 1)]

/-- Direct kernel `rfl` boundary checks on the literal pinned `nimTriples` (`n = 1..4`) and
equation-lemma verification of the literal pinned `a063915` (`m = 0..31`). -/
theorem literal_kernel_boundary_checks :
    nimTriples 1 = 0 ∧ nimTriples 2 = 0 ∧ nimTriples 3 = 1 ∧ nimTriples 4 = 1 ∧
    (List.range' 0 32).map a063915 =
      [1, 3, 5, 9, 13, 17, 21, 29, 37, 45, 53, 61, 69, 77, 85, 101,
       117, 133, 149, 165, 181, 197, 213, 229, 245, 261, 277, 293, 309, 325, 341, 373] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp [List.range', a063915, a063915Aux]

/-- Kernel-verified spot checks of `nimTriples n` across all `n = 1..32` (`SCOPING-S006.md` §2.4)
and flat steps `nimTriples (2^m) = nimTriples (2^m - 1)` for `m = 1..6` via the independently
proved computable mirror `nimTriplesFast_eq_nimTriples`. -/
theorem nimTriples_spot_checks_1_to_32 :
    (List.range' 1 32).map nimTriples =
      [0, 0, 1, 1, 2, 4, 7, 7, 8, 10, 13, 17, 22, 28, 35, 35,
       36, 38, 41, 45, 50, 56, 63, 71, 80, 90, 101, 113, 126, 140, 155, 155] ∧
    ([1, 2, 3, 4, 5, 6].map (fun m => (nimTriples (2 ^ m), nimTriples (2 ^ m - 1))) =
      [(0, 0), (1, 1), (7, 7), (35, 35), (155, 155), (651, 651)]) := by
  have hfun : nimTriples = nimTriplesFast := funext (fun n => (nimTriplesFast_eq_nimTriples n).symm)
  rw [hfun]
  exact ⟨rfl, rfl⟩

end SeamC.A363166
