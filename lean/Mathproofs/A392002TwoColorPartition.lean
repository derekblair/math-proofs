import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.PNat.Basic

/-!
# Seam C Entry S001 (OEIS A392002): Two-Color Partition Odd-Color-Sum Identity

Formalizes and proves Thomas Hutton's conjectured generating-function identity on `OEIS A392002`
(`%F` lines 12–13, Dec 26 2025; live revision `#11 Jan 01 2026 17:33:09`) against the frozen
target contract `PIN-S001.md` v1 (`delta_vs_source: NONE`), following the sign-reversing
color-parity involution and halving-bijection route in `TRIAGE-SEAMC.md` (§2.2 S001, §3.2, and
Table 1.3 / Table 5.1):

`∀ n : ℕ, 2 * a n = p₂ n - (if Even n then p (n / 2) else 0)`

where `p` is the ordinary partition function (`OEIS A000041`), `p₂` is the 2-colored partition
function (`OEIS A000712`), and `a` counts `{0,1}`-colored partitions of `n` whose color sum
(`length(λ⁽¹⁾)`, the number of `1`-colored parts — NOT the sum of their sizes) is odd.
-/

namespace SeamC.A392002

open scoped BigOperators

/-! ### Section 1: Pinned Target Definitions (`PIN-S001.md` v1) -/

/-- A `{0,1}`-colored partition of `n` (`n ≥ 0`), represented per `PIN-S001.md` (`fidelity_notes`)
and `TRIAGE-SEAMC.md` (§5.1) as a pair of ordinary partitions `(λ⁽⁰⁾, λ⁽¹⁾)` of `(k₀, k₁)` with
`k₀ + k₁ = n` (`(k₀, k₁) ∈ Finset.antidiagonal n`), where `λ⁽⁰⁾` consists of the `0`-colored parts
and `λ⁽¹⁾` consists of the `1`-colored parts. -/
abbrev TwoColorPartition (n : ℕ) : Type :=
  Σ k : Finset.antidiagonal n, Nat.Partition k.1.1 × Nat.Partition k.1.2

/-- Color sum `∑ c = length(λ⁽¹⁾)`: the number of `1`-colored parts (not the sum of their sizes). -/
def colorSum {n : ℕ} (π : TwoColorPartition n) : ℕ :=
  π.2.2.parts.card

/-- `OEIS A000041`: the ordinary partition function `p(n)`. -/
def p (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

/-- `OEIS A000712`: the number `p₂(n)` of `{0,1}`-colored partitions of `n`. -/
def p₂ (n : ℕ) : ℕ :=
  Fintype.card (TwoColorPartition n)

/-- `OEIS A392002`: the number `a(n)` of `{0,1}`-colored partitions of `n` whose color sum is odd. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun π : TwoColorPartition n => Odd (colorSum π))).card

/-! ### Section 2: Equivalence with Colored Multisets (`ℕ+ × Fin 2`) & `A000712` Convolution -/

/-- `OEIS A000712` convolution formula: `p₂ n = ∑ k ∈ Finset.range (n + 1), p k * p (n - k)`. -/
theorem p₂_eq_sum_range (n : ℕ) :
    p₂ n = ∑ k ∈ Finset.range (n + 1), p k * p (n - k) := by
  unfold p₂ TwoColorPartition p
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod]
  rw [Finset.univ_eq_attach, Finset.sum_attach (Finset.antidiagonal n) (fun x =>
    Fintype.card (Nat.Partition x.1) * Fintype.card (Nat.Partition x.2))]
  rw [Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  rfl

/-- Flat pair-of-multisets model of a `{0,1}`-colored partition of `n`, eliminating dependent
antidiagonal indices while keeping `parts₀` (`0`-colored parts) and `parts₁` (`1`-colored parts)
explicit. -/
@[ext]
structure PartPair (n : ℕ) where
  parts₀ : Multiset ℕ
  parts₁ : Multiset ℕ
  pos₀ : ∀ {i}, i ∈ parts₀ → 0 < i
  pos₁ : ∀ {i}, i ∈ parts₁ → 0 < i
  sum_eq : parts₀.sum + parts₁.sum = n
deriving DecidableEq

/-- Canonical bijection between `TwoColorPartition n` and `PartPair n`. -/
def equivPartPair (n : ℕ) : TwoColorPartition n ≃ PartPair n where
  toFun π :=
    { parts₀ := π.2.1.parts
      parts₁ := π.2.2.parts
      pos₀ := π.2.1.parts_pos
      pos₁ := π.2.2.parts_pos
      sum_eq := by
        rw [π.2.1.parts_sum, π.2.2.parts_sum]
        exact Finset.mem_antidiagonal.mp π.1.2 }
  invFun x :=
    ⟨⟨(x.parts₀.sum, x.parts₁.sum), Finset.mem_antidiagonal.mpr x.sum_eq⟩,
      (⟨x.parts₀, x.pos₀, rfl⟩, ⟨x.parts₁, x.pos₁, rfl⟩)⟩
  left_inv π := by
    rcases π with ⟨⟨⟨k₀, k₁⟩, hk⟩, ⟨p0, p1⟩⟩
    dsimp only at p0 p1 ⊢
    rcases p0 with ⟨m0, hm0, rfl⟩
    rcases p1 with ⟨m1, hm1, rfl⟩
    rfl
  right_inv x := by
    ext <;> rfl

instance (n : ℕ) : Fintype (PartPair n) :=
  Fintype.ofEquiv (TwoColorPartition n) (equivPartPair n)

@[simp]
theorem equivPartPair_parts₁_card {n : ℕ} (π : TwoColorPartition n) :
    (equivPartPair n π).parts₁.card = colorSum π :=
  rfl

theorem card_partPair_eq_p₂ (n : ℕ) : Fintype.card (PartPair n) = p₂ n :=
  Fintype.card_congr (equivPartPair n).symm

theorem card_odd_partPair_eq_a (n : ℕ) :
    (Finset.univ.filter (fun x : PartPair n => Odd x.parts₁.card)).card = a n := by
  unfold a
  refine Finset.card_bij (fun x _ => (equivPartPair n).symm x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    simpa [colorSum, equivPartPair] using hx
  · intro x₁ _ x₂ _ h
    exact (equivPartPair n).symm.injective h
  · intro π hπ
    refine ⟨equivPartPair n π, ?_, (equivPartPair n).symm_apply_apply π⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    exact hπ

/-- Finite multiset of colored parts `(s, c) ∈ ℕ+ × Fin 2` whose sizes sum to `n`
(`PIN-S001.md` `fidelity_notes` L44–46). -/
@[ext]
structure ColoredMultiset (n : ℕ) where
  parts : Multiset (ℕ+ × Fin 2)
  parts_sum : (parts.map (fun x => (x.1 : ℕ))).sum = n
deriving DecidableEq

/-- Color sum `∑ c` on `ColoredMultiset n`. -/
def ColoredMultiset.colorSum {n : ℕ} (m : ColoredMultiset n) : ℕ :=
  (m.parts.map (fun x => (x.2 : ℕ))).sum

/-- Lift a multiset of positive natural numbers to `Multiset (ℕ+ × Fin 2)` with fixed color `c`. -/
def liftColored (c : Fin 2) (s : Multiset ℕ) : Multiset (ℕ+ × Fin 2) :=
  s.map (fun i => ((⟨max i 1, by omega⟩ : ℕ+), c))

theorem map_fst_liftColored (c : Fin 2) (s : Multiset ℕ) (hs : ∀ {i}, i ∈ s → 0 < i) :
    (liftColored c s).map (fun x => (x.1 : ℕ)) = s := by
  unfold liftColored
  rw [Multiset.map_map]
  refine (Multiset.map_congr rfl (fun i hi => ?_)).trans (Multiset.map_id' s)
  have hpos : 0 < i := hs hi
  change max i 1 = i
  omega

@[simp]
theorem map_snd_liftColored (c : Fin 2) (s : Multiset ℕ) :
    (liftColored c s).map (fun x => (x.2 : ℕ)) = Multiset.replicate s.card (c : ℕ) := by
  unfold liftColored
  rw [Multiset.map_map]
  refine (Multiset.map_congr rfl (fun _ _ => rfl)).trans ?_
  exact Multiset.map_const' s (c : ℕ)

@[simp]
theorem filter_eq_self_liftColored (c : Fin 2) (s : Multiset ℕ) :
    (liftColored c s).filter (fun x => x.2 = c) = liftColored c s := by
  rw [Multiset.filter_eq_self]
  intro x hx
  unfold liftColored at hx
  rcases Multiset.mem_map.mp hx with ⟨a, _, rfl⟩
  rfl

@[simp]
theorem filter_ne_liftColored {c d : Fin 2} (hcd : c ≠ d) (s : Multiset ℕ) :
    (liftColored c s).filter (fun x => x.2 = d) = 0 := by
  rw [Multiset.filter_eq_nil]
  intro x hx
  unfold liftColored at hx
  rcases Multiset.mem_map.mp hx with ⟨a, _, rfl⟩
  exact hcd

private theorem fin2_eq_one_iff_ne_zero (c : Fin 2) : c = 1 ↔ ¬ c = 0 := by
  rcases c with ⟨val, hlt⟩
  omega

/-- Canonical equivalence between `PartPair n` and `ColoredMultiset n`, certifying equivalence of
the pair-of-partitions and `Multiset (ℕ+ × Fin 2)` models in `PIN-S001.md`. -/
def partPairEquivColoredMultiset (n : ℕ) : PartPair n ≃ ColoredMultiset n where
  toFun x :=
    { parts := liftColored 0 x.parts₀ + liftColored 1 x.parts₁
      parts_sum := by
        rw [Multiset.map_add, Multiset.sum_add, map_fst_liftColored 0 x.parts₀ x.pos₀,
          map_fst_liftColored 1 x.parts₁ x.pos₁, x.sum_eq] }
  invFun m :=
    { parts₀ := (m.parts.filter (fun x => x.2 = 0)).map (fun x => (x.1 : ℕ))
      parts₁ := (m.parts.filter (fun x => x.2 = 1)).map (fun x => (x.1 : ℕ))
      pos₀ := by
        intro i hi
        rcases Multiset.mem_map.mp hi with ⟨x, _, rfl⟩
        exact x.1.2
      pos₁ := by
        intro i hi
        rcases Multiset.mem_map.mp hi with ⟨x, _, rfl⟩
        exact x.1.2
      sum_eq := by
        have hflt : m.parts.filter (fun x => x.2 = 1) = m.parts.filter (fun x => ¬ x.2 = 0) :=
          Multiset.filter_congr (fun x _ => fin2_eq_one_iff_ne_zero x.2)
        rw [hflt, ← Multiset.sum_add, ← Multiset.map_add, Multiset.filter_add_not]
        exact m.parts_sum }
  left_inv x := by
    ext i
    · dsimp only
      rw [Multiset.filter_add, filter_eq_self_liftColored,
        filter_ne_liftColored (by decide : (1 : Fin 2) ≠ 0), add_zero,
        map_fst_liftColored 0 x.parts₀ x.pos₀]
    · dsimp only
      rw [Multiset.filter_add, filter_ne_liftColored (by decide : (0 : Fin 2) ≠ 1),
        filter_eq_self_liftColored, zero_add, map_fst_liftColored 1 x.parts₁ x.pos₁]
  right_inv m := by
    ext x
    have hflt : m.parts.filter (fun y => y.2 = 1) = m.parts.filter (fun y => ¬ y.2 = 0) :=
      Multiset.filter_congr (fun y _ => fin2_eq_one_iff_ne_zero y.2)
    have hlift : ∀ (c : Fin 2),
        liftColored c ((m.parts.filter (fun y => y.2 = c)).map (fun y => (y.1 : ℕ))) =
        m.parts.filter (fun y => y.2 = c) := by
      intro c
      unfold liftColored
      rw [Multiset.map_map]
      refine (Multiset.map_congr rfl (fun y hy => ?_)).trans (Multiset.map_id' _)
      rcases Multiset.mem_filter.mp hy with ⟨_, rfl⟩
      rcases y with ⟨⟨v, hv⟩, col⟩
      dsimp only [Function.comp_apply, id_eq]
      refine Prod.ext (Subtype.ext ?_) rfl
      change max v 1 = v
      omega
    dsimp only
    rw [hlift 0, hlift 1, hflt, Multiset.filter_add_not]

/-- Equivalence between `TwoColorPartition n` and `ColoredMultiset n`, preserving color sum. -/
def equivColoredMultiset (n : ℕ) : TwoColorPartition n ≃ ColoredMultiset n :=
  (equivPartPair n).trans (partPairEquivColoredMultiset n)

theorem colorSum_eq_coloredMultiset_colorSum {n : ℕ} (π : TwoColorPartition n) :
    colorSum π = (equivColoredMultiset n π).colorSum := by
  change π.2.2.parts.card =
    ((liftColored 0 π.2.1.parts + liftColored 1 π.2.2.parts).map (fun x => (x.2 : ℕ))).sum
  rw [Multiset.map_add, Multiset.sum_add, map_snd_liftColored, map_snd_liftColored]
  simp

/-! ### Section 3: Stage 1 — Least-Odd-Total-Multiplicity Swap Involution (`swapLeastOdd`) -/

/-- Support finset of part sizes `j` whose total multiplicity `m_{j,0} + m_{j,1}` in `x` is odd. -/
def oddTotalSizes {n : ℕ} (x : PartPair n) : Finset ℕ :=
  (x.parts₀ + x.parts₁).toFinset.filter (fun j => Odd (x.parts₀.count j + x.parts₁.count j))

theorem mem_oddTotalSizes {n : ℕ} (x : PartPair n) (j : ℕ) :
    j ∈ oddTotalSizes x ↔ Odd (x.parts₀.count j + x.parts₁.count j) := by
  unfold oddTotalSizes
  rw [Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_add]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  by_contra hmem
  rw [not_or] at hmem
  have h0 : x.parts₀.count j = 0 := Multiset.count_eq_zero.mpr hmem.1
  have h1 : x.parts₁.count j = 0 := Multiset.count_eq_zero.mpr hmem.2
  rw [h0, h1] at h
  exact Nat.not_odd_zero h

/-- Swap all `0`-colored and `1`-colored occurrences of part size `j`, mapping
`(m_{j,0}, m_{j,1}) ↦ (m_{j,1}, m_{j,0})` while leaving all `k ≠ j` unchanged. -/
def swapAt {n : ℕ} (j : ℕ) (x : PartPair n) : PartPair n where
  parts₀ := x.parts₁.filter (· = j) + x.parts₀.filter (· ≠ j)
  parts₁ := x.parts₀.filter (· = j) + x.parts₁.filter (· ≠ j)
  pos₀ := by
    intro i hi
    rcases Multiset.mem_add.mp hi with h | h
    · exact x.pos₁ (Multiset.mem_of_mem_filter h)
    · exact x.pos₀ (Multiset.mem_of_mem_filter h)
  pos₁ := by
    intro i hi
    rcases Multiset.mem_add.mp hi with h | h
    · exact x.pos₀ (Multiset.mem_of_mem_filter h)
    · exact x.pos₁ (Multiset.mem_of_mem_filter h)
  sum_eq := by
    have h0 : (x.parts₀.filter (· = j)).sum + (x.parts₀.filter (· ≠ j)).sum = x.parts₀.sum := by
      rw [← Multiset.sum_add]
      exact congrArg Multiset.sum (Multiset.filter_add_not (· = j) x.parts₀)
    have h1 : (x.parts₁.filter (· = j)).sum + (x.parts₁.filter (· ≠ j)).sum = x.parts₁.sum := by
      rw [← Multiset.sum_add]
      exact congrArg Multiset.sum (Multiset.filter_add_not (· = j) x.parts₁)
    rw [Multiset.sum_add, Multiset.sum_add]
    have hx := x.sum_eq
    omega

theorem count₀_swapAt_self {n : ℕ} (j : ℕ) (x : PartPair n) :
    (swapAt j x).parts₀.count j = x.parts₁.count j := by
  simp [swapAt]

theorem count₁_swapAt_self {n : ℕ} (j : ℕ) (x : PartPair n) :
    (swapAt j x).parts₁.count j = x.parts₀.count j := by
  simp [swapAt]

theorem count₀_swapAt_of_ne {n : ℕ} {j k : ℕ} (hk : k ≠ j) (x : PartPair n) :
    (swapAt j x).parts₀.count k = x.parts₀.count k := by
  simp [swapAt, hk]

theorem count₁_swapAt_of_ne {n : ℕ} {j k : ℕ} (hk : k ≠ j) (x : PartPair n) :
    (swapAt j x).parts₁.count k = x.parts₁.count k := by
  simp [swapAt, hk]

theorem total_count_swapAt {n : ℕ} (j k : ℕ) (x : PartPair n) :
    (swapAt j x).parts₀.count k + (swapAt j x).parts₁.count k =
      x.parts₀.count k + x.parts₁.count k := by
  by_cases hk : k = j
  · subst hk
    rw [count₀_swapAt_self, count₁_swapAt_self, add_comm]
  · rw [count₀_swapAt_of_ne hk, count₁_swapAt_of_ne hk]

@[simp]
theorem oddTotalSizes_swapAt {n : ℕ} (j : ℕ) (x : PartPair n) :
    oddTotalSizes (swapAt j x) = oddTotalSizes x := by
  ext k
  rw [mem_oddTotalSizes, mem_oddTotalSizes, total_count_swapAt]

@[simp]
theorem swapAt_involutive {n : ℕ} (j : ℕ) (x : PartPair n) :
    swapAt j (swapAt j x) = x := by
  ext k
  · by_cases hk : k = j
    · subst hk; rw [count₀_swapAt_self, count₁_swapAt_self]
    · rw [count₀_swapAt_of_ne hk, count₀_swapAt_of_ne hk]
  · by_cases hk : k = j
    · subst hk; rw [count₁_swapAt_self, count₀_swapAt_self]
    · rw [count₁_swapAt_of_ne hk, count₁_swapAt_of_ne hk]

theorem card_parts₁_swapAt_add {n : ℕ} (j : ℕ) (x : PartPair n) :
    (swapAt j x).parts₁.card + x.parts₁.card =
      (x.parts₀.count j + x.parts₁.count j) + 2 * (x.parts₁.filter (· ≠ j)).card := by
  have hx1 : x.parts₁.card = (x.parts₁.filter (· = j)).card + (x.parts₁.filter (· ≠ j)).card := by
    rw [← Multiset.card_add]
    exact congrArg Multiset.card (Multiset.filter_add_not (· = j) x.parts₁).symm
  have hs1 : (swapAt j x).parts₁.card =
      (x.parts₀.filter (· = j)).card + (x.parts₁.filter (· ≠ j)).card := by
    simp [swapAt]
  have hc0 : (x.parts₀.filter (· = j)).card = x.parts₀.count j := by
    rw [Multiset.count_eq_card_filter_eq]
    exact congrArg Multiset.card (Multiset.filter_congr (fun a _ => eq_comm))
  have hc1 : (x.parts₁.filter (· = j)).card = x.parts₁.count j := by
    rw [Multiset.count_eq_card_filter_eq]
    exact congrArg Multiset.card (Multiset.filter_congr (fun a _ => eq_comm))
  omega

/-- Stage 1 involution (`TRIAGE-SEAMC.md` §3.2): at the least `j` with `m_{j,0} + m_{j,1}` odd,
swap `(m_{j,0}, m_{j,1}) ↦ (m_{j,1}, m_{j,0})`. -/
def swapLeastOdd {n : ℕ} (x : PartPair n) : PartPair n :=
  if h : (oddTotalSizes x).Nonempty then
    swapAt ((oddTotalSizes x).min' h) x
  else
    x

theorem swapLeastOdd_involutive {n : ℕ} : Function.Involutive (swapLeastOdd (n := n)) := by
  intro x
  unfold swapLeastOdd
  split_ifs with h h'
  · have hmin : (oddTotalSizes (swapAt ((oddTotalSizes x).min' h) x)).min' h' =
        (oddTotalSizes x).min' h := by
      congr 1
      exact oddTotalSizes_swapAt _ _
    rw [hmin, swapAt_involutive]
  · exfalso
    rw [oddTotalSizes_swapAt] at h'
    exact h' h
  · rfl

theorem swapLeastOdd_fixed_iff {n : ℕ} (x : PartPair n) :
    swapLeastOdd x = x ↔ ∀ j : ℕ, Even (x.parts₀.count j + x.parts₁.count j) := by
  constructor
  · intro hfix j
    rw [← Nat.not_odd_iff_even]
    intro hodd
    have hne : (oddTotalSizes x).Nonempty := ⟨j, (mem_oddTotalSizes x j).mpr hodd⟩
    unfold swapLeastOdd at hfix
    simp only [hne, ↓reduceDIte] at hfix
    set j₀ := (oddTotalSizes x).min' hne
    have hj₀ : Odd (x.parts₀.count j₀ + x.parts₁.count j₀) :=
      (mem_oddTotalSizes x j₀).mp ((oddTotalSizes x).min'_mem hne)
    have hsum := card_parts₁_swapAt_add j₀ x
    rw [hfix] at hsum
    rcases hj₀ with ⟨k, hk⟩
    omega
  · intro heven
    have hempty : oddTotalSizes x = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      exact (Nat.not_odd_iff_even.mpr (heven j)) ((mem_oddTotalSizes x j).mp hj)
    unfold swapLeastOdd
    simp [hempty]

/-! ### Section 4: Stage 2 — Even-Total-Multiplicity Fiber Involution & `colorParityInvolution` -/

/-- Support finset of part sizes `j` having at least one `1`-colored occurrence (`m_{j,1} > 0`). -/
def posOneSizes {n : ℕ} (x : PartPair n) : Finset ℕ :=
  x.parts₁.toFinset

theorem mem_posOneSizes {n : ℕ} (x : PartPair n) (j : ℕ) :
    j ∈ posOneSizes x ↔ 0 < x.parts₁.count j := by
  unfold posOneSizes
  rw [Multiset.mem_toFinset, Multiset.count_pos]

/-- On an even-total-multiplicity fiber (`m_{j,0} + m_{j,1} = 2k`), pair nonzero `1`-multiplicities
`{1, 2}, {3, 4}, …, {2k - 1, 2k}` by moving one part of size `j` from `parts₀` to `parts₁` when
`m_{j,1}` is odd, and from `parts₁` to `parts₀` when `m_{j,1} > 0` is even. -/
def shiftEvenFiberAt {n : ℕ} (j : ℕ) (x : PartPair n) : PartPair n :=
  if Odd (x.parts₁.count j) then
    if hj0 : j ∈ x.parts₀ then
      { parts₀ := x.parts₀.erase j
        parts₁ := j ::ₘ x.parts₁
        pos₀ := fun hi => x.pos₀ (Multiset.mem_of_mem_erase hi)
        pos₁ := fun hi => by
          rcases Multiset.mem_cons.mp hi with rfl | h
          · exact x.pos₀ hj0
          · exact x.pos₁ h
        sum_eq := by
          have hs0 : j + (x.parts₀.erase j).sum = x.parts₀.sum := by
            simpa using congrArg Multiset.sum (Multiset.cons_erase hj0)
          rw [Multiset.sum_cons]
          have hx := x.sum_eq
          omega }
    else x
  else
    if hj1 : j ∈ x.parts₁ then
      { parts₀ := j ::ₘ x.parts₀
        parts₁ := x.parts₁.erase j
        pos₀ := fun hi => by
          rcases Multiset.mem_cons.mp hi with rfl | h
          · exact x.pos₁ hj1
          · exact x.pos₀ h
        pos₁ := fun hi => x.pos₁ (Multiset.mem_of_mem_erase hi)
        sum_eq := by
          have hs1 : j + (x.parts₁.erase j).sum = x.parts₁.sum := by
            simpa using congrArg Multiset.sum (Multiset.cons_erase hj1)
          rw [Multiset.sum_cons]
          have hx := x.sum_eq
          omega }
    else x

theorem shiftEvenFiberAt_props {n : ℕ} {x : PartPair n} {j : ℕ}
    (heven : ∀ k : ℕ, Even (x.parts₀.count k + x.parts₁.count k))
    (hj : 0 < x.parts₁.count j) :
    oddTotalSizes (shiftEvenFiberAt j x) = ∅ ∧
    posOneSizes (shiftEvenFiberAt j x) = posOneSizes x ∧
    shiftEvenFiberAt j (shiftEvenFiberAt j x) = x ∧
    (Odd (shiftEvenFiberAt j x).parts₁.card ↔ ¬ Odd x.parts₁.card) ∧
    shiftEvenFiberAt j x ≠ x := by
  have htot := heven j
  by_cases hodd1 : Odd (x.parts₁.count j)
  · have hj0_pos : 0 < x.parts₀.count j := by
      rcases htot with ⟨m, hm⟩
      rcases hodd1 with ⟨q, hq⟩
      omega
    have hj0 : j ∈ x.parts₀ := Multiset.count_pos.mp hj0_pos
    set y := shiftEvenFiberAt j x with hy_def
    have hy0 : y.parts₀ = x.parts₀.erase j := by
      rw [hy_def]; unfold shiftEvenFiberAt; simp [hodd1, hj0]
    have hy1 : y.parts₁ = j ::ₘ x.parts₁ := by
      rw [hy_def]; unfold shiftEvenFiberAt; simp [hodd1, hj0]
    have hy_tot : ∀ k : ℕ, Even (y.parts₀.count k + y.parts₁.count k) := by
      intro k
      rw [hy0, hy1]
      by_cases hkj : k = j
      · subst hkj
        rw [Multiset.count_erase_self, Multiset.count_cons_self]
        rcases htot with ⟨m, hm⟩
        refine ⟨m, ?_⟩
        omega
      · rw [Multiset.count_erase_of_ne hkj, Multiset.count_cons_of_ne hkj]
        exact heven k
    have hy_odd_empty : oddTotalSizes y = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      exact (Nat.not_odd_iff_even.mpr (hy_tot k)) ((mem_oddTotalSizes y k).mp hk)
    have hy_pos : posOneSizes y = posOneSizes x := by
      ext k
      rw [mem_posOneSizes, mem_posOneSizes, hy1]
      by_cases hkj : k = j
      · subst hkj
        simp [hj]
      · rw [Multiset.count_cons_of_ne hkj]
    have hy_not_odd : ¬ Odd (y.parts₁.count j) := by
      rw [hy1, Multiset.count_cons_self]
      rcases hodd1 with ⟨q, hq⟩
      rw [Nat.not_odd_iff_even]
      exact ⟨q + 1, by omega⟩
    have hj_mem_y1 : j ∈ y.parts₁ := by
      rw [hy1]
      exact Multiset.mem_cons_self j x.parts₁
    have hinv : shiftEvenFiberAt j y = x := by
      ext k
      · have h : (shiftEvenFiberAt j y).parts₀ = j ::ₘ y.parts₀ := by
          unfold shiftEvenFiberAt; simp [hy_not_odd, hj_mem_y1]
        rw [h, hy0, Multiset.cons_erase hj0]
      · have h : (shiftEvenFiberAt j y).parts₁ = y.parts₁.erase j := by
          unfold shiftEvenFiberAt; simp [hy_not_odd, hj_mem_y1]
        rw [h, hy1, Multiset.erase_cons_head]
    have hcard : y.parts₁.card = x.parts₁.card + 1 := by
      rw [hy1, Multiset.card_cons]
    refine ⟨hy_odd_empty, hy_pos, hinv, ?_, ?_⟩
    · rw [hcard, Nat.odd_add_one]
    · intro heq
      rw [heq] at hcard
      omega
  · have hj1_ge2 : 2 ≤ x.parts₁.count j := by
      rw [Nat.not_odd_iff_even] at hodd1
      rcases hodd1 with ⟨q, hq⟩
      omega
    have hj1 : j ∈ x.parts₁ := Multiset.count_pos.mp hj
    set y := shiftEvenFiberAt j x with hy_def
    have hy0 : y.parts₀ = j ::ₘ x.parts₀ := by
      rw [hy_def]; unfold shiftEvenFiberAt; simp [hodd1, hj1]
    have hy1 : y.parts₁ = x.parts₁.erase j := by
      rw [hy_def]; unfold shiftEvenFiberAt; simp [hodd1, hj1]
    have hy_tot : ∀ k : ℕ, Even (y.parts₀.count k + y.parts₁.count k) := by
      intro k
      rw [hy0, hy1]
      by_cases hkj : k = j
      · subst hkj
        rw [Multiset.count_cons_self, Multiset.count_erase_self]
        rcases htot with ⟨m, hm⟩
        refine ⟨m, ?_⟩
        omega
      · rw [Multiset.count_cons_of_ne hkj, Multiset.count_erase_of_ne hkj]
        exact heven k
    have hy_odd_empty : oddTotalSizes y = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      exact (Nat.not_odd_iff_even.mpr (hy_tot k)) ((mem_oddTotalSizes y k).mp hk)
    have hy_pos : posOneSizes y = posOneSizes x := by
      ext k
      rw [mem_posOneSizes, mem_posOneSizes, hy1]
      by_cases hkj : k = j
      · subst hkj
        rw [Multiset.count_erase_self]
        omega
      · rw [Multiset.count_erase_of_ne hkj]
    have hy_odd : Odd (y.parts₁.count j) := by
      rw [hy1, Multiset.count_erase_self]
      rw [Nat.not_odd_iff_even] at hodd1
      rcases hodd1 with ⟨q, hq⟩
      refine ⟨q - 1, ?_⟩
      omega
    have hj_mem_y0 : j ∈ y.parts₀ := by
      rw [hy0]
      exact Multiset.mem_cons_self j x.parts₀
    have hinv : shiftEvenFiberAt j y = x := by
      ext k
      · have h : (shiftEvenFiberAt j y).parts₀ = y.parts₀.erase j := by
          unfold shiftEvenFiberAt; simp [hy_odd, hj_mem_y0]
        rw [h, hy0, Multiset.erase_cons_head]
      · have h : (shiftEvenFiberAt j y).parts₁ = j ::ₘ y.parts₁ := by
          unfold shiftEvenFiberAt; simp [hy_odd, hj_mem_y0]
        rw [h, hy1, Multiset.cons_erase hj1]
    have hcard : y.parts₁.card + 1 = x.parts₁.card := by
      rw [hy1]
      exact Multiset.card_erase_add_one hj1
    refine ⟨hy_odd_empty, hy_pos, hinv, ?_, ?_⟩
    · rw [← hcard, Nat.odd_add_one, not_not]
    · intro heq
      rw [heq] at hcard
      omega

/-- Unified sign-reversing color-parity involution on `PartPair n`:
1. Off the even-total-multiplicity locus (`(oddTotalSizes x).Nonempty`), swaps
   `(m_{j,0}, m_{j,1}) ↦ (m_{j,1}, m_{j,0})` at the least `j` with `m_{j,0} + m_{j,1}` odd.
2. On the even-total-multiplicity locus (`∀ j, Even (m_{j,0} + m_{j,1})`), pairs nonzero `1`-counts
   at the least `j` with `m_{j,1} > 0`, leaving fixed solely the all-`0`-colored doubled partitions
   (`parts₁ = 0` and `∀ j, Even (parts₀.count j)`). -/
def colorParityInvolution {n : ℕ} (x : PartPair n) : PartPair n :=
  if h : (oddTotalSizes x).Nonempty then
    swapAt ((oddTotalSizes x).min' h) x
  else if h1 : (posOneSizes x).Nonempty then
    shiftEvenFiberAt ((posOneSizes x).min' h1) x
  else
    x

theorem colorParityInvolution_involutive {n : ℕ} :
    Function.Involutive (colorParityInvolution (n := n)) := by
  intro x
  by_cases h : (oddTotalSizes x).Nonempty
  · have hd : colorParityInvolution x = swapAt ((oddTotalSizes x).min' h) x := by
      unfold colorParityInvolution; simp only [h, ↓reduceDIte]
    rw [hd]
    have h' : (oddTotalSizes (swapAt ((oddTotalSizes x).min' h) x)).Nonempty := by
      rwa [oddTotalSizes_swapAt]
    unfold colorParityInvolution
    simp only [h', ↓reduceDIte]
    have hmin : (oddTotalSizes (swapAt ((oddTotalSizes x).min' h) x)).min' h' =
        (oddTotalSizes x).min' h := by
      congr 1
      exact oddTotalSizes_swapAt _ _
    rw [hmin, swapAt_involutive]
  · have heven : ∀ k : ℕ, Even (x.parts₀.count k + x.parts₁.count k) := by
      intro k
      rw [← Nat.not_odd_iff_even]
      intro hodd
      exact h ⟨k, (mem_oddTotalSizes x k).mpr hodd⟩
    by_cases h1 : (posOneSizes x).Nonempty
    · have hd : colorParityInvolution x = shiftEvenFiberAt ((posOneSizes x).min' h1) x := by
        unfold colorParityInvolution; simp only [h, h1, ↓reduceDIte]
      rw [hd]
      set j₀ := (posOneSizes x).min' h1
      have hj₀ : 0 < x.parts₁.count j₀ :=
        (mem_posOneSizes x j₀).mp ((posOneSizes x).min'_mem h1)
      obtain ⟨hodd_empty, hpos_eq, hinv, _, _⟩ := shiftEvenFiberAt_props heven hj₀
      have h_y : ¬ (oddTotalSizes (shiftEvenFiberAt j₀ x)).Nonempty := by
        rw [hodd_empty]; simp
      have h1_y : (posOneSizes (shiftEvenFiberAt j₀ x)).Nonempty := by
        rwa [hpos_eq]
      unfold colorParityInvolution
      simp only [h_y, h1_y, ↓reduceDIte]
      have hmin : (posOneSizes (shiftEvenFiberAt j₀ x)).min' h1_y = j₀ := by
        congr 1
      rw [hmin]
      exact hinv
    · have hd : colorParityInvolution x = x := by
        unfold colorParityInvolution; simp only [h, h1, ↓reduceDIte]
      rw [hd, hd]

theorem colorParityInvolution_nonfixed_parity {n : ℕ} {x : PartPair n}
    (hne : colorParityInvolution x ≠ x) :
    Odd (colorParityInvolution x).parts₁.card ↔ ¬ Odd x.parts₁.card := by
  by_cases h : (oddTotalSizes x).Nonempty
  · have hd : colorParityInvolution x = swapAt ((oddTotalSizes x).min' h) x := by
      unfold colorParityInvolution; simp only [h, ↓reduceDIte]
    rw [hd]
    set j₀ := (oddTotalSizes x).min' h
    have hj₀ : Odd (x.parts₀.count j₀ + x.parts₁.count j₀) :=
      (mem_oddTotalSizes x j₀).mp ((oddTotalSizes x).min'_mem h)
    have hsum := card_parts₁_swapAt_add j₀ x
    rcases hj₀ with ⟨k, hk⟩
    constructor
    · rintro ⟨q, hq⟩ ⟨r, hr⟩; omega
    · intro hnot
      rw [Nat.not_odd_iff_even] at hnot
      rcases hnot with ⟨r, hr⟩
      exact ⟨k + (x.parts₁.filter (· ≠ j₀)).card - r, by omega⟩
  · have heven : ∀ k : ℕ, Even (x.parts₀.count k + x.parts₁.count k) := by
      intro k
      rw [← Nat.not_odd_iff_even]
      intro hodd
      exact h ⟨k, (mem_oddTotalSizes x k).mpr hodd⟩
    by_cases h1 : (posOneSizes x).Nonempty
    · have hd : colorParityInvolution x = shiftEvenFiberAt ((posOneSizes x).min' h1) x := by
        unfold colorParityInvolution; simp only [h, h1, ↓reduceDIte]
      rw [hd]
      set j₀ := (posOneSizes x).min' h1
      have hj₀ : 0 < x.parts₁.count j₀ :=
        (mem_posOneSizes x j₀).mp ((posOneSizes x).min'_mem h1)
      exact (shiftEvenFiberAt_props heven hj₀).2.2.2.1
    · exfalso
      apply hne
      unfold colorParityInvolution
      simp only [h, h1, ↓reduceDIte]

theorem colorParityInvolution_fixed_iff {n : ℕ} (x : PartPair n) :
    colorParityInvolution x = x ↔ x.parts₁ = 0 ∧ ∀ j : ℕ, Even (x.parts₀.count j) := by
  constructor
  · intro hfix
    have h_no_odd : ¬ (oddTotalSizes x).Nonempty := by
      intro h
      have hd : colorParityInvolution x = swapAt ((oddTotalSizes x).min' h) x := by
        unfold colorParityInvolution; simp only [h, ↓reduceDIte]
      set j₀ := (oddTotalSizes x).min' h
      have hj₀ : Odd (x.parts₀.count j₀ + x.parts₁.count j₀) :=
        (mem_oddTotalSizes x j₀).mp ((oddTotalSizes x).min'_mem h)
      have hsum := card_parts₁_swapAt_add j₀ x
      rw [← hd, hfix] at hsum
      rcases hj₀ with ⟨k, hk⟩
      omega
    have heven : ∀ k : ℕ, Even (x.parts₀.count k + x.parts₁.count k) := by
      intro k
      rw [← Nat.not_odd_iff_even]
      intro hodd
      exact h_no_odd ⟨k, (mem_oddTotalSizes x k).mpr hodd⟩
    have h_no_one : ¬ (posOneSizes x).Nonempty := by
      intro h1
      have hd : colorParityInvolution x = shiftEvenFiberAt ((posOneSizes x).min' h1) x := by
        unfold colorParityInvolution; simp only [h_no_odd, h1, ↓reduceDIte]
      set j₀ := (posOneSizes x).min' h1
      have hj₀ : 0 < x.parts₁.count j₀ :=
        (mem_posOneSizes x j₀).mp ((posOneSizes x).min'_mem h1)
      have hne := (shiftEvenFiberAt_props heven hj₀).2.2.2.2
      rw [← hd] at hne
      exact hne hfix
    have hp1 : x.parts₁ = 0 := by
      ext j
      simp only [Multiset.count_zero]
      by_contra hj
      exact h_no_one ⟨j, (mem_posOneSizes x j).mpr (Nat.pos_of_ne_zero hj)⟩
    refine ⟨hp1, fun j => ?_⟩
    have hj := heven j
    simpa [hp1] using hj
  · rintro ⟨hp1, heven0⟩
    have h_no_odd : ¬ (oddTotalSizes x).Nonempty := by
      rintro ⟨j, hj⟩
      have hodd := (mem_oddTotalSizes x j).mp hj
      rw [hp1, Multiset.count_zero, add_zero] at hodd
      exact (Nat.not_odd_iff_even.mpr (heven0 j)) hodd
    have h_no_one : ¬ (posOneSizes x).Nonempty := by
      rintro ⟨j, hj⟩
      have hpos := (mem_posOneSizes x j).mp hj
      simp [hp1] at hpos
    unfold colorParityInvolution
    simp only [h_no_odd, h_no_one, ↓reduceDIte]

theorem not_odd_of_fixed {n : ℕ} {x : PartPair n} (hfix : colorParityInvolution x = x) :
    ¬ Odd x.parts₁.card := by
  obtain ⟨hp1, _⟩ := (colorParityInvolution_fixed_iff x).mp hfix
  simp [hp1]

/-! ### Section 5: The Halving Bijection & Fixed-Point Count -/

/-- Halve every multiplicity in a multiset `m : Multiset ℕ`. -/
def halfMultiset (m : Multiset ℕ) : Multiset ℕ :=
  ∑ k ∈ m.toFinset, Multiset.replicate (m.count k / 2) k

@[simp]
theorem count_halfMultiset (m : Multiset ℕ) (x : ℕ) :
    (halfMultiset m).count x = m.count x / 2 := by
  unfold halfMultiset
  rw [Multiset.count_sum']
  by_cases hx : x ∈ m.toFinset
  · rw [Finset.sum_eq_single x]
    · simp
    · intro k _ hkx
      simp [Multiset.count_replicate, hkx]
    · intro hnot
      exact absurd hx hnot
  · rw [Finset.sum_eq_zero]
    · have h0 : m.count x = 0 := by
        rw [Multiset.mem_toFinset] at hx
        exact Multiset.count_eq_zero.mpr hx
      simp [h0]
    · intro k hk
      have hkx : k ≠ x := fun h => hx (h ▸ hk)
      simp [Multiset.count_replicate, hkx]

theorem halfMultiset_add_self {m : Multiset ℕ} (heven : ∀ x : ℕ, Even (m.count x)) :
    halfMultiset m + halfMultiset m = m := by
  ext x
  rw [Multiset.count_add, count_halfMultiset]
  rcases heven x with ⟨q, hq⟩
  omega

/-- No fixed point can exist when `n` is odd. -/
theorem fixed_empty_of_not_even {n : ℕ} (hn : ¬ Even n) (x : PartPair n) :
    colorParityInvolution x ≠ x := by
  intro hfix
  obtain ⟨hp1, heven0⟩ := (colorParityInvolution_fixed_iff x).mp hfix
  have hdouble := congrArg Multiset.sum (halfMultiset_add_self heven0)
  rw [Multiset.sum_add] at hdouble
  have hsum := x.sum_eq
  rw [hp1, Multiset.sum_zero, add_zero] at hsum
  exact hn ⟨(halfMultiset x.parts₀).sum, by omega⟩

/-- The halving bijection: when `n` is even, fixed points of `colorParityInvolution` on
`PartPair n` are in canonical bijection with ordinary partitions `Nat.Partition (n / 2)`. -/
def fixedEquivPartitionHalf {n : ℕ} (hn : Even n) :
    { x : PartPair n // colorParityInvolution x = x } ≃ Nat.Partition (n / 2) where
  toFun x :=
    let hfix := (colorParityInvolution_fixed_iff x.1).mp x.2
    { parts := halfMultiset x.1.parts₀
      parts_pos := by
        intro i hi
        have hpos : 0 < (halfMultiset x.1.parts₀).count i := Multiset.count_pos.mpr hi
        rw [count_halfMultiset] at hpos
        have hpos0 : 0 < x.1.parts₀.count i := by omega
        exact x.1.pos₀ (Multiset.count_pos.mp hpos0)
      parts_sum := by
        have hdouble := congrArg Multiset.sum (halfMultiset_add_self hfix.2)
        rw [Multiset.sum_add] at hdouble
        have hsum := x.1.sum_eq
        rw [hfix.1, Multiset.sum_zero, add_zero] at hsum
        rcases hn with ⟨m, rfl⟩
        omega }
  invFun μ :=
    ⟨{ parts₀ := μ.parts + μ.parts
       parts₁ := 0
       pos₀ := by
         intro i hi
         rcases Multiset.mem_add.mp hi with h | h <;> exact μ.parts_pos h
       pos₁ := by simp
       sum_eq := by
         rw [Multiset.sum_add, Multiset.sum_zero, μ.parts_sum]
         rcases hn with ⟨m, rfl⟩
         omega },
     (colorParityInvolution_fixed_iff _).mpr ⟨rfl, fun j => ⟨μ.parts.count j, by
       simp [Multiset.count_add]⟩⟩⟩
  left_inv x := by
    obtain ⟨hp1, heven0⟩ := (colorParityInvolution_fixed_iff x.1).mp x.2
    apply Subtype.ext
    ext k
    · dsimp only
      have h := halfMultiset_add_self heven0
      exact congrArg (fun m => m.count k) h
    · dsimp only
      simp [hp1]
  right_inv μ := by
    ext k
    dsimp only
    rw [count_halfMultiset, Multiset.count_add]
    omega

theorem card_fixed_partPair (n : ℕ) :
    (Finset.univ.filter (fun x : PartPair n => colorParityInvolution x = x)).card =
      if Even n then p (n / 2) else 0 := by
  split_ifs with hn
  · unfold p
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (fixedEquivPartitionHalf hn)
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    exact fixed_empty_of_not_even hn x

/-! ### Section 6: Double Counting & Pinned Theorem (`two_mul_oddColorPartitions_eq`) -/

/-- Decomposition `p₂ n = 2 * a n + (if Even n then p (n / 2) else 0)` obtained by partitioning
`PartPair n` into odd-color-sum elements, paired non-fixed even-color-sum elements, and fixed
points of `colorParityInvolution`. -/
theorem p₂_eq_two_mul_a_add_fixed (n : ℕ) :
    p₂ n = 2 * a n + (if Even n then p (n / 2) else 0) := by
  let oddSet : Finset (PartPair n) :=
    Finset.univ.filter (fun x => Odd x.parts₁.card)
  let pairedEvenSet : Finset (PartPair n) :=
    Finset.univ.filter (fun x => ¬ Odd x.parts₁.card ∧ colorParityInvolution x ≠ x)
  let fixedSet : Finset (PartPair n) :=
    Finset.univ.filter (fun x => colorParityInvolution x = x)
  have h_image : pairedEvenSet = oddSet.image colorParityInvolution := by
    ext y
    simp only [pairedEvenSet, oddSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨hnot_odd, hne⟩
      refine ⟨colorParityInvolution y, ?_, colorParityInvolution_involutive y⟩
      exact (colorParityInvolution_nonfixed_parity hne).mpr hnot_odd
    · rintro ⟨x, hx_odd, rfl⟩
      have hne : colorParityInvolution x ≠ x := fun hfix => not_odd_of_fixed hfix hx_odd
      have hne_y : colorParityInvolution (colorParityInvolution x) ≠ colorParityInvolution x := by
        rw [colorParityInvolution_involutive]
        exact hne.symm
      have hnot_odd : ¬ Odd (colorParityInvolution x).parts₁.card := by
        intro hy_odd
        exact ((colorParityInvolution_nonfixed_parity hne).mp hy_odd) hx_odd
      exact ⟨hnot_odd, hne_y⟩
  have h_inj : Function.Injective (colorParityInvolution (n := n)) :=
    (colorParityInvolution_involutive (n := n)).injective
  have h_card_paired : pairedEvenSet.card = oddSet.card := by
    rw [h_image]
    exact Finset.card_image_of_injOn h_inj.injOn
  have h_disj₁ : Disjoint oddSet pairedEvenSet := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [oddSet, pairedEvenSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
    exact hx₂.1 hx₁
  have h_disj₂ : Disjoint (oddSet ∪ pairedEvenSet) fixedSet := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [oddSet, pairedEvenSet, fixedSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx₁ hx₂
    rcases hx₁ with hodd | ⟨_, hne⟩
    · exact not_odd_of_fixed hx₂ hodd
    · exact hne hx₂
  have h_union : (oddSet ∪ pairedEvenSet) ∪ fixedSet = Finset.univ := by
    ext x
    simp only [oddSet, pairedEvenSet, fixedSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    by_cases hfix : colorParityInvolution x = x
    · exact Or.inr hfix
    · by_cases hodd : Odd x.parts₁.card
      · exact Or.inl (Or.inl hodd)
      · exact Or.inl (Or.inr ⟨hodd, hfix⟩)
  have h_total : Fintype.card (PartPair n) =
      oddSet.card + pairedEvenSet.card + fixedSet.card := by
    rw [← Finset.card_univ, ← h_union, Finset.card_union_of_disjoint h_disj₂,
      Finset.card_union_of_disjoint h_disj₁]
  rw [← card_partPair_eq_p₂ n, h_total, h_card_paired, card_odd_partPair_eq_a n,
    card_fixed_partPair n]
  omega

/-- Thomas Hutton's `OEIS A392002` identity (`%F` lines 12–13): for every `n : ℕ`, twice the
number of `{0,1}`-colored partitions of `n` with odd color sum equals
`p₂ n - (if Even n then p (n / 2) else 0)`. -/
theorem two_mul_oddColorPartitions_eq :
    ∀ n : ℕ, 2 * a n = p₂ n - (if Even n then p (n / 2) else 0) := by
  intro n
  have h := p₂_eq_two_mul_a_add_fixed n
  omega

/-! ### Section 7: Boundary Cases, Verified Computable DP Mirror, and Semantic Traps -/

theorem p_zero : p 0 = 1 :=
  Fintype.card_unique

theorem p_one : p 1 = 1 :=
  Fintype.card_unique

theorem p₂_zero : p₂ 0 = 1 := by
  rw [p₂_eq_sum_range, Finset.sum_range_one, Nat.sub_zero, p_zero]

/-- At `n = 0`, the unique empty `{0,1}`-colored partition has color sum `0` (even), so `a 0 = 0`
(`PIN-S001.md` `fidelity_notes` L47–48: `2 * 0 = 1 - 1`). -/
theorem a_zero : a 0 = 0 := by
  unfold a colorSum
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨⟨⟨k₀, k₁⟩, hk⟩, ⟨_, p1⟩⟩ _
  have hk01 : k₀ + k₁ = 0 := Finset.mem_antidiagonal.mp hk
  have hk1 : k₁ = 0 := by omega
  dsimp only at p1 ⊢
  subst hk1
  simp

theorem p₂_one : p₂ 1 = 2 := by
  rw [p₂_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_one]
  simp [p_zero, p_one]

/-- Inner structural fuel loop for bounded-part partition counting (pure `Nat.rec`, kernel
`rfl`-reducible without `WellFounded.fix`). -/
def pByParityAux (prev : ℕ → Bool → ℕ) (step : ℕ) : ℕ → ℕ → Bool → ℕ
  | 0, n, b => prev n b
  | fuel + 1, n, b =>
    prev n b + (if step ≤ n then pByParityAux prev step fuel (n - step) (!b) else 0)

theorem pByParityAux_eq_of_le (prev : ℕ → Bool → ℕ) {step : ℕ} (hstep : 0 < step) :
    ∀ (fuel : ℕ) {n : ℕ} (b : Bool), n ≤ fuel →
      pByParityAux prev step (fuel + 1) n b = pByParityAux prev step fuel n b
  | 0, n, b, hn => by
    have hn0 : n = 0 := by omega
    subst hn0
    have hnot : ¬ step ≤ 0 := by omega
    simp [pByParityAux, hnot]
  | fuel + 1, n, b, hn => by
    rw [pByParityAux]
    conv_rhs => rw [pByParityAux]
    split_ifs with hle
    · have hsub : n - step ≤ fuel := by omega
      rw [pByParityAux_eq_of_le prev hstep fuel (!b) hsub]
    · rfl

/-- Bounded-part partition DP stratified by part-count parity, defined by structural recursion on
`m` (`pByParity m n b` counts partitions of `n` into parts `≤ m` with `decide (Odd parts.card) = b`). -/
def pByParity : ℕ → ℕ → Bool → ℕ
  | 0, 0, b => if b then 0 else 1
  | 0, _ + 1, _ => 0
  | m + 1, n, b => pByParityAux (pByParity m) (m + 1) n n b

theorem pByParity_succ_m (m n : ℕ) (b : Bool) :
    pByParity (m + 1) n b =
      pByParity m n b + (if m + 1 ≤ n then pByParity (m + 1) (n - (m + 1)) (!b) else 0) := by
  cases n with
  | zero =>
    simp [pByParity, pByParityAux]
  | succ n' =>
    rw [pByParity, pByParityAux]
    congr 1
    split_ifs with hle
    · have h_iter : ∀ d : ℕ, (n' + 1 - (m + 1)) + d ≤ n' →
          pByParityAux (pByParity m) (m + 1) ((n' + 1 - (m + 1)) + d)
            (n' + 1 - (m + 1)) (!b) =
          pByParityAux (pByParity m) (m + 1) (n' + 1 - (m + 1))
            (n' + 1 - (m + 1)) (!b) := by
        intro d
        induction d with
        | zero => intro _; rfl
        | succ d ih =>
          intro hd
          rw [← Nat.add_assoc,
            pByParityAux_eq_of_le (pByParity m) (Nat.succ_pos m)
              (n' + 1 - (m + 1) + d) (!b) (Nat.le_add_right _ _)]
          exact ih (by omega)
      have heq := h_iter m (by omega)
      have hidx : (n' + 1 - (m + 1)) + m = n' := by omega
      rw [hidx] at heq
      rw [heq]
      cases hsub : n' + 1 - (m + 1) <;> rfl
    · rfl

/-- Finset of ordinary partitions of `n` with parts `≤ m` and `decide (Odd parts.card) = b`. -/
def restrictedParity (n m : ℕ) (b : Bool) : Finset n.Partition :=
  Finset.univ.filter (fun μ : n.Partition =>
    (∀ i ∈ μ.parts, i ≤ m) ∧ decide (Odd μ.parts.card) = b)

theorem pByParity_eq_card :
    ∀ (m n : ℕ) (b : Bool), pByParity m n b = (restrictedParity n m b).card
  | 0, 0, b => by
    unfold pByParity restrictedParity
    cases b
    · have huniv : (Finset.univ.filter (fun μ : Nat.Partition 0 =>
          (∀ i ∈ μ.parts, i ≤ 0) ∧ decide (Odd μ.parts.card) = false)) = Finset.univ := by
        ext μ
        simp
      rw [huniv, Finset.card_univ]
      exact Fintype.card_unique.symm
    · simp only [↓reduceIte]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro μ _
      simp
  | 0, n + 1, b => by
    unfold pByParity restrictedParity
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro μ _ ⟨hle, _⟩
    have hne : μ.parts ≠ 0 := by
      intro h0
      have hs := μ.parts_sum
      rw [h0, Multiset.sum_zero] at hs
      omega
    obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero hne
    have hpos := μ.parts_pos hi
    have hi0 := hle i hi
    omega
  | m + 1, n, b => by
    rw [pByParity_succ_m]
    let S := restrictedParity n (m + 1) b
    have hsplit : S.card =
        (S.filter (fun μ => m + 1 ∈ μ.parts)).card +
        (S.filter (fun μ => m + 1 ∉ μ.parts)).card :=
      (Finset.card_filter_add_card_filter_not (fun μ : n.Partition => m + 1 ∈ μ.parts)).symm
    have h_not_mem : S.filter (fun μ => m + 1 ∉ μ.parts) = restrictedParity n m b := by
      ext μ
      simp only [S, restrictedParity, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hle, hb⟩, hnot⟩
        refine ⟨fun i hi => ?_, hb⟩
        have h1 := hle i hi
        have hne : i ≠ m + 1 := fun heq => hnot (heq ▸ hi)
        omega
      · rintro ⟨hle, hb⟩
        refine ⟨⟨fun i hi => by have := hle i hi; omega, hb⟩, fun hm => ?_⟩
        have := hle (m + 1) hm
        omega
    rw [show (restrictedParity n (m + 1) b).card = S.card from rfl,
      hsplit, h_not_mem, ← pByParity_eq_card m n b, add_comm]
    congr 1
    split_ifs with hmn
    · rw [pByParity_eq_card (m + 1) (n - (m + 1)) (!b)]
      symm
      refine Finset.card_bij
        (fun μ hμ =>
          let hm_mem : m + 1 ∈ μ.parts := (Finset.mem_filter.mp hμ).2
          { parts := μ.parts.erase (m + 1)
            parts_pos := fun hi => μ.parts_pos (Multiset.mem_of_mem_erase hi)
            parts_sum := by
              have hs : (m + 1) + (μ.parts.erase (m + 1)).sum = n := by
                simpa [μ.parts_sum] using congrArg Multiset.sum (Multiset.cons_erase hm_mem)
              omega })
        ?_ ?_ ?_
      · intro μ hμ
        rcases Finset.mem_filter.mp hμ with ⟨hS, hm_mem⟩
        rcases Finset.mem_filter.mp hS with ⟨_, hle, hb⟩
        rw [restrictedParity, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun i hi => hle i (Multiset.mem_of_mem_erase hi), ?_⟩
        dsimp only
        have hcard : (μ.parts.erase (m + 1)).card + 1 = μ.parts.card :=
          Multiset.card_erase_add_one hm_mem
        have hodd : Odd (μ.parts.erase (m + 1)).card ↔ ¬ Odd μ.parts.card := by
          rw [← hcard, Nat.odd_add_one, not_not]
        cases b
        · simp only [Bool.not_false, decide_eq_true_eq] at hb ⊢
          rw [decide_eq_false_iff_not] at hb
          exact hodd.mpr hb
        · simp only [Bool.not_true, decide_eq_false_iff_not] at hb ⊢
          rw [decide_eq_true_eq] at hb
          exact fun ho => hodd.mp ho hb
      · intro μ₁ hμ₁ μ₂ hμ₂ heq
        have hm₁ : m + 1 ∈ μ₁.parts := (Finset.mem_filter.mp hμ₁).2
        have hm₂ : m + 1 ∈ μ₂.parts := (Finset.mem_filter.mp hμ₂).2
        have hp : μ₁.parts.erase (m + 1) = μ₂.parts.erase (m + 1) :=
          congrArg Nat.Partition.parts heq
        have hc := congrArg ((m + 1) ::ₘ ·) hp
        rw [Multiset.cons_erase hm₁, Multiset.cons_erase hm₂] at hc
        exact Nat.Partition.ext hc
      · intro ν hν
        rcases Finset.mem_filter.mp hν with ⟨_, hle, hb⟩
        let μ : n.Partition :=
          { parts := (m + 1) ::ₘ ν.parts
            parts_pos := by
              intro i hi
              rcases Multiset.mem_cons.mp hi with rfl | h
              · omega
              · exact ν.parts_pos h
            parts_sum := by
              rw [Multiset.sum_cons, ν.parts_sum]
              omega }
        refine ⟨μ, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨?_, Multiset.mem_cons_self (m + 1) ν.parts⟩
          dsimp only [S]
          rw [restrictedParity, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · intro i hi
            rcases Multiset.mem_cons.mp hi with rfl | h
            · exact le_rfl
            · exact hle i h
          · have hcard : μ.parts.card = ν.parts.card + 1 := Multiset.card_cons (m + 1) ν.parts
            rw [hcard]
            cases b
            · simp only [Bool.not_false, decide_eq_true_eq] at hb
              rw [decide_eq_false_iff_not, Nat.odd_add_one, not_not]
              exact hb
            · simp only [Bool.not_true, decide_eq_false_iff_not] at hb
              rw [decide_eq_true_eq, Nat.odd_add_one]
              exact hb
        · ext k
          dsimp only [μ]
          rw [Multiset.erase_cons_head]
    · symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro μ _ hm_mem
      have hle := Nat.Partition.le_of_mem_parts hm_mem
      omega
termination_by m n => (m, n)

/-- Computable bounded-part mirror of `p n` (`OEIS A000041`). -/
def p_dp (n : ℕ) : ℕ :=
  pByParity n n false + pByParity n n true

theorem p_dp_eq_p (n : ℕ) : p_dp n = p n := by
  unfold p_dp p
  rw [pByParity_eq_card, pByParity_eq_card]
  have hfalse : restrictedParity n n false =
      Finset.univ.filter (fun μ : n.Partition => ¬ decide (Odd μ.parts.card) = true) := by
    ext μ
    simp only [restrictedParity, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.not_eq_true]
    exact ⟨fun h => h.2, fun h => ⟨fun _ hi => Nat.Partition.le_of_mem_parts hi, h⟩⟩
  have htrue : restrictedParity n n true =
      Finset.univ.filter (fun μ : n.Partition => decide (Odd μ.parts.card) = true) := by
    ext μ
    simp only [restrictedParity, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨fun _ hi => Nat.Partition.le_of_mem_parts hi, h⟩⟩
  rw [hfalse, htrue, add_comm,
    Finset.card_filter_add_card_filter_not (fun μ : n.Partition =>
      decide (Odd μ.parts.card) = true),
    Finset.card_univ]

/-- Computable mirror counting ordinary partitions of `k` with an odd number of parts. -/
def pOdd_dp (k : ℕ) : ℕ :=
  pByParity k k true

theorem pOdd_dp_eq_card_odd (k : ℕ) :
    pOdd_dp k = (Finset.univ.filter (fun μ : k.Partition => Odd μ.parts.card)).card := by
  unfold pOdd_dp
  rw [pByParity_eq_card]
  congr 1
  ext μ
  simp only [restrictedParity, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨fun _ hi => Nat.Partition.le_of_mem_parts hi, h⟩⟩

/-- Structural-recursion finite sum `∑ k ≤ m, f k` for kernel `rfl` evaluation. -/
def sumUpTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | m + 1 => sumUpTo f m + f (m + 1)

theorem sumUpTo_eq_sum_range (f : ℕ → ℕ) (m : ℕ) :
    sumUpTo f m = ∑ k ∈ Finset.range (m + 1), f k := by
  induction m with
  | zero => simp [sumUpTo]
  | succ m ih => rw [sumUpTo, ih, ← Finset.sum_range_succ]

/-- Computable mirror of `p₂ n` (`OEIS A000712`). -/
def p₂_dp (n : ℕ) : ℕ :=
  sumUpTo (fun k => p_dp k * p_dp (n - k)) n

theorem p₂_dp_eq_p₂ (n : ℕ) : p₂_dp n = p₂ n := by
  unfold p₂_dp
  rw [sumUpTo_eq_sum_range, p₂_eq_sum_range]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [p_dp_eq_p, p_dp_eq_p]

/-- Computable mirror of `a n` (`OEIS A392002`), defined directly from the pair-of-partitions
definition (`Odd λ⁽¹⁾.parts.card`) WITHOUT invoking `two_mul_oddColorPartitions_eq`. -/
def a_dp (n : ℕ) : ℕ :=
  sumUpTo (fun k => p_dp k * pOdd_dp (n - k)) n

theorem a_eq_sum_range_oddParts (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1),
      p k * (Finset.univ.filter (fun μ : (n - k).Partition => Odd μ.parts.card)).card := by
  unfold a p colorSum
  have hsigma :
      (Finset.univ : Finset (TwoColorPartition n)).filter
        (fun π => Odd π.2.2.parts.card) =
      (Finset.univ : Finset (Finset.antidiagonal n)).sigma
        (fun k => (Finset.univ : Finset k.1.1.Partition) ×ˢ
          (Finset.univ.filter (fun μ : k.1.2.Partition => Odd μ.parts.card))) := by
    ext ⟨k, p0, p1⟩
    simp
  rw [hsigma, Finset.card_sigma]
  simp only [Finset.card_product, Finset.card_univ]
  rw [Finset.univ_eq_attach, Finset.sum_attach (Finset.antidiagonal n) (fun x : ℕ × ℕ =>
    Fintype.card x.1.Partition *
      (Finset.univ.filter (fun μ : x.2.Partition => Odd μ.parts.card)).card)]
  rw [Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  rfl

theorem a_dp_eq_a (n : ℕ) : a_dp n = a n := by
  unfold a_dp
  rw [sumUpTo_eq_sum_range, a_eq_sum_range_oddParts]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [p_dp_eq_p, pOdd_dp_eq_card_odd]

/-- Kernel `rfl` verification of `a_dp` on `n = 0..12` against printed `OEIS A392002`. -/
theorem a_dp_spot_0_to_12 :
    [a_dp 0, a_dp 1, a_dp 2, a_dp 3, a_dp 4, a_dp 5, a_dp 6,
     a_dp 7, a_dp 8, a_dp 9, a_dp 10, a_dp 11, a_dp 12] =
    [0, 1, 2, 5, 9, 18, 31, 55, 90, 150, 237, 376, 577] :=
  rfl

/-- Kernel verification of `SeamC.A392002.a` on `n = 0..12` transferred via `a_dp_eq_a`. -/
theorem a_spot_0_to_12 :
    [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10, a 11, a 12] =
    [0, 1, 2, 5, 9, 18, 31, 55, 90, 150, 237, 376, 577] := by
  simp only [← a_dp_eq_a]
  exact a_dp_spot_0_to_12

/-- Kernel verification of `SeamC.A392002.p₂` (`OEIS A000712`) on `n = 0..12`. -/
theorem p₂_spot_0_to_12 :
    [p₂ 0, p₂ 1, p₂ 2, p₂ 3, p₂ 4, p₂ 5, p₂ 6, p₂ 7, p₂ 8, p₂ 9, p₂ 10, p₂ 11, p₂ 12] =
    [1, 2, 5, 10, 20, 36, 65, 110, 185, 300, 481, 752, 1165] := by
  simp only [← p₂_dp_eq_p₂]
  rfl

/-- Kernel verification of `SeamC.A392002.p` (`OEIS A000041`) on `n = 0..12`. -/
theorem p_spot_0_to_12 :
    [p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, p 8, p 9, p 10, p 11, p 12] =
    [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77] := by
  simp only [← p_dp_eq_p]
  rfl

/-- **The Color-Sum Trap** (`BRIEF` §1 / `ownharness` S001 note): misreading "color sum" as the
sum of sizes `|λ⁽¹⁾| = k₁` rather than the number of `1`-colored parts `length(λ⁽¹⁾)` agrees with
`a n` at `n = 0` and at every odd `n`, but fails at `n = 2` (`1 ≠ 2`) and at all positive even `n`. -/
def aWrongSizeSum (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun π : TwoColorPartition n => Odd π.1.1.2)).card

theorem aWrongSizeSum_two_eq_one_ne_a_two :
    aWrongSizeSum 2 = 1 ∧ aWrongSizeSum 2 ≠ a 2 := by
  have ha2 : a 2 = 2 := by rw [← a_dp_eq_a]; rfl
  have hw : aWrongSizeSum 2 =
      ∑ k ∈ Finset.range 3, p k * (if Odd (2 - k) then p (2 - k) else 0) := by
    unfold aWrongSizeSum p
    have hsigma :
        (Finset.univ : Finset (TwoColorPartition 2)).filter (fun π => Odd π.1.1.2) =
        (Finset.univ : Finset (Finset.antidiagonal 2)).sigma
          (fun k => (Finset.univ : Finset k.1.1.Partition) ×ˢ
            (if Odd k.1.2 then (Finset.univ : Finset k.1.2.Partition) else ∅)) := by
      ext ⟨k, p0, p1⟩
      by_cases ho : Odd k.1.2 <;> simp [ho]
    rw [hsigma, Finset.card_sigma]
    simp only [Finset.card_product, Finset.card_univ]
    rw [Finset.univ_eq_attach, Finset.sum_attach (Finset.antidiagonal 2) (fun x : ℕ × ℕ =>
      Fintype.card x.1.Partition *
        (if Odd x.2 then (Finset.univ : Finset x.2.Partition) else ∅).card)]
    rw [Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    change Fintype.card k.Partition *
        (if Odd (2 - k) then (Finset.univ : Finset (2 - k).Partition) else ∅).card = _
    split_ifs <;> simp
  have hp1 : p 1 = 1 := p_one
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hw
  have ho2 : ¬ Odd 2 := by decide
  have ho1 : Odd 1 := by decide
  have ho0 : ¬ Odd 0 := by decide
  simp only [Nat.sub_zero, ho2, ↓reduceIte, mul_zero, show 2 - 1 = 1 from rfl, ho1,
    Nat.sub_self, ho0, hp1, mul_one, zero_add, add_zero] at hw
  exact ⟨hw, by omega⟩

end SeamC.A392002
