import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Seam B Entry C037 (OEIS A203568): Peter Bala's Rogers–Fine Polynomial Family

Formalizes and proves Peter Bala's February 11, 2021 conjectural `N`-parameterized
generating-function family on `OEIS A203568` (`%F` lines 24–26, live revision `#52 Feb 18 2021`;
companions `OEIS A026837` `%I #20`, `OEIS A026838` `%I #24`, `OEIS A143062` `%I #58`, and
`OEIS A186424` `%I #52`) against the frozen target contract `PIN-C037.md` v1
(`delta_vs_source: NONE`), following the `Step 0 + Links 1–4` route from `SCOPING-C037.md` (§2.2).
-/

namespace Mathproofs.A203568RogersFineFamily

open scoped BigOperators Classical Polynomial PowerSeries PowerSeries.WithPiTopology

noncomputable section

/-! ### Pinned Target Definitions (`PIN-C037.md` v1) -/

/-- `OEIS A026837`: number of partitions `p ∈ Nat.Partition.distincts n` of `n` into distinct
parts whose greatest part is odd (`0` at `n = 0`). -/
def a026837 (n : ℕ) : ℕ :=
  ((Nat.Partition.distincts n).filter
    (fun p ↦ ∃ m ∈ p.parts, Odd m ∧ ∀ x ∈ p.parts, x ≤ m)).card

/-- `OEIS A026838`: number of partitions `p ∈ Nat.Partition.distincts n` of `n` into distinct
parts whose greatest part is even (`0` at `n = 0`). -/
def a026838 (n : ℕ) : ℕ :=
  ((Nat.Partition.distincts n).filter
    (fun p ↦ ∃ m ∈ p.parts, Even m ∧ ∀ x ∈ p.parts, x ≤ m)).card

/-- `OEIS A203568` (`%N`): `a(n) = A026837(n) - A026838(n)` with offset `0` and `a(0) = 0`. -/
def a203568 (n : ℕ) : ℤ :=
  (a026837 n : ℤ) - (a026838 n : ℤ)

/-- Formal power series `A(X) = ∑_{n ≥ 0} A203568(n) X^n` in `ℤ⟦X⟧`. -/
def a203568Series : ℤ⟦X⟧ :=
  PowerSeries.mk a203568

/-- Explicit polynomial family `P(N, X) ∈ ℤ[X]` pinned by `c037Poly 0 = 0`, `c037Poly 1 = 0`, and
`c037Poly (N + 1) = (1 + X ^ (2 * N)) * c037Poly N + (-1) ^ (N + 1) * X ^ N` for all `N ≥ 1`. -/
def c037Poly : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 0
  | N + 2 =>
      (1 + Polynomial.X ^ (2 * (N + 1))) * c037Poly (N + 1) +
        (-1) ^ (N + 2) * Polynomial.X ^ (N + 1)

/-! ### Section 1: Finite-Interval, Unit-Reciprocal, and Locally-Finite `HasSum` Helpers -/

private lemma finset_Icc_succ_right {a b : ℕ} (h : a ≤ b + 1) :
    Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

private lemma finset_Icc_of_gt {a b : ℕ} (h : b < a) :
    Finset.Icc a b = ∅ := by
  ext x
  simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]
  omega

private lemma finset_Icc_one_eq_map_range (n : ℕ) :
    Finset.Icc 1 n = (Finset.range n).map ⟨(· + 1), add_left_injective 1⟩ := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · intro hx
    exact ⟨x - 1, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    omega

private lemma c037Poly_succ {N : ℕ} (hN : 1 ≤ N) :
    c037Poly (N + 1) =
      (1 + Polynomial.X ^ (2 * N)) * c037Poly N + (-1) ^ (N + 1) * Polynomial.X ^ N := by
  cases N with
  | zero => omega
  | succ k => rfl

private abbrev inv1 (φ : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  PowerSeries.invOfUnit φ (1 : ℤˣ)

private lemma constantCoeff_X_pow_pos {k : ℕ} (hk : 0 < k) :
    PowerSeries.constantCoeff ((PowerSeries.X : ℤ⟦X⟧) ^ k) = 0 := by
  cases k with
  | zero => omega
  | succ m => simp [pow_succ]

private lemma constantCoeff_one_add_X_pow {k : ℕ} (hk : 0 < k) :
    PowerSeries.constantCoeff (1 + (PowerSeries.X : ℤ⟦X⟧) ^ k) = 1 := by
  rw [map_add, map_one, constantCoeff_X_pow_pos hk, add_zero]

private lemma constantCoeff_prod_one_add {ι : Type*} (s : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ s, 0 < e i) :
    PowerSeries.constantCoeff (∏ i ∈ s, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ e i)) = 1 := by
  rw [map_prod]
  exact Finset.prod_eq_one fun i hi ↦ constantCoeff_one_add_X_pow (he i hi)

private lemma mul_inv1 {φ : ℤ⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 1) :
    φ * inv1 φ = 1 :=
  PowerSeries.mul_invOfUnit φ (1 : ℤˣ) (by simpa using hφ)

private lemma inv1_mul {φ : ℤ⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 1) :
    inv1 φ * φ = 1 :=
  PowerSeries.invOfUnit_mul φ (1 : ℤˣ) (by simpa using hφ)

private lemma inv1_one : inv1 (1 : ℤ⟦X⟧) = 1 := by
  have h := inv1_mul (φ := (1 : ℤ⟦X⟧)) (map_one _)
  simpa using h

private lemma inv1_mul_distrib {φ ψ : ℤ⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 1) (hψ : PowerSeries.constantCoeff ψ = 1) :
    inv1 (φ * ψ) = inv1 φ * inv1 ψ := by
  have hφψ : PowerSeries.constantCoeff (φ * ψ) = 1 := by
    rw [map_mul, hφ, hψ, mul_one]
  calc
    inv1 (φ * ψ) = inv1 (φ * ψ) * ((φ * ψ) * (inv1 φ * inv1 ψ)) := by
      have : (φ * ψ) * (inv1 φ * inv1 ψ) = 1 := by
        calc
          (φ * ψ) * (inv1 φ * inv1 ψ) = (φ * inv1 φ) * (ψ * inv1 ψ) := by ring
          _ = 1 * 1 := by rw [mul_inv1 hφ, mul_inv1 hψ]
          _ = 1 := mul_one 1
      rw [this, mul_one]
    _ = (inv1 (φ * ψ) * (φ * ψ)) * (inv1 φ * inv1 ψ) := by ring
    _ = inv1 φ * inv1 ψ := by rw [inv1_mul hφψ, one_mul]

private lemma mul_inv1_cancel_right {φ ψ : ℤ⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 1) (hψ : PowerSeries.constantCoeff ψ = 1) :
    ψ * inv1 (φ * ψ) = inv1 φ := by
  rw [inv1_mul_distrib hφ hψ]
  calc
    ψ * (inv1 φ * inv1 ψ) = inv1 φ * (ψ * inv1 ψ) := by ring
    _ = inv1 φ * 1 := by rw [mul_inv1 hψ]
    _ = inv1 φ := mul_one _

private lemma mul_inv1_cancel_left {φ ψ : ℤ⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 1) (hψ : PowerSeries.constantCoeff ψ = 1) :
    φ * inv1 (φ * ψ) = inv1 ψ := by
  rw [mul_comm φ ψ]
  exact mul_inv1_cancel_right hψ hφ

private lemma coeff_X_pow_mul_eq_zero {e d : ℕ} (hd : d < e) (ψ : ℤ⟦X⟧) :
    PowerSeries.coeff d ((PowerSeries.X : ℤ⟦X⟧) ^ e * ψ) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  have hle : ¬ e ≤ d := by omega
  simp [hle]

private lemma hasSum_mk_of_coeff_vanish (f : ℕ → ℤ⟦X⟧) (B : ℕ → ℕ)
    (hvanish : ∀ d m : ℕ, B d ≤ m → PowerSeries.coeff d (f m) = 0) :
    HasSum f (PowerSeries.mk fun d ↦ ∑ m ∈ Finset.range (B d), PowerSeries.coeff d (f m)) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  rw [PowerSeries.coeff_mk]
  refine hasSum_sum_of_ne_finset_zero fun m hm ↦ ?_
  rw [Finset.mem_range, not_lt] at hm
  exact hvanish d m hm

private lemma hasSum_of_sub_eq_and_coeff_zero (R t : ℕ → ℤ⟦X⟧)
    (hstep : ∀ M : ℕ, R M - R (M + 1) = t M)
    (hzero : ∀ d M : ℕ, d < M → PowerSeries.coeff d (R M) = 0) :
    HasSum t (R 0) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  have hfin : HasSum (fun M ↦ PowerSeries.coeff d (t M))
      (∑ M ∈ Finset.range (d + 1), PowerSeries.coeff d (t M)) := by
    refine hasSum_sum_of_ne_finset_zero fun M hM ↦ ?_
    rw [Finset.mem_range, not_lt] at hM
    rw [← hstep M, map_sub, hzero d M (by omega), hzero d (M + 1) (by omega), sub_zero]
  have htel : ∑ M ∈ Finset.range (d + 1), PowerSeries.coeff d (t M) =
      PowerSeries.coeff d (R 0) := by
    have hcongr : ∀ M ∈ Finset.range (d + 1),
        PowerSeries.coeff d (t M) =
          PowerSeries.coeff d (R M) - PowerSeries.coeff d (R (M + 1)) := by
      intro M _
      rw [← hstep M, map_sub]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_range_sub' (fun M ↦ PowerSeries.coeff d (R M)),
      hzero d (d + 1) (by omega), sub_zero]
  rwa [htel] at hfin

/-! ### Section 2: Polynomial Family `c037Poly` Helpers -/

private lemma deg_step_arith {M : ℕ} (hM : 2 ≤ M) :
    2 * M + (M ^ 2 - M - 1) = (M + 1) ^ 2 - (M + 1) - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
  have h1 : (k + 2) ^ 2 - (k + 2) - 1 = k ^ 2 + 3 * k + 1 := by
    have : (k + 2) ^ 2 = (k ^ 2 + 3 * k + 1) + (k + 2) + 1 := by ring
    omega
  have h2 : (k + 2 + 1) ^ 2 - (k + 2 + 1) - 1 = k ^ 2 + 3 * k + 1 + 2 * (k + 2) := by
    have : (k + 2 + 1) ^ 2 = (k ^ 2 + 3 * k + 1 + 2 * (k + 2)) + (k + 2 + 1) + 1 := by ring
    omega
  rw [h1, h2]
  ring

private lemma lt_deg_step_arith {M : ℕ} (hM : 2 ≤ M) :
    M < (M + 1) ^ 2 - (M + 1) - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
  have h2 : (k + 2 + 1) ^ 2 - (k + 2 + 1) - 1 = k ^ 2 + 5 * k + 5 := by
    have : (k + 2 + 1) ^ 2 = (k ^ 2 + 5 * k + 5) + (k + 2 + 1) + 1 := by ring
    omega
  rw [h2]
  omega

private lemma neg_one_pow_mul_X_pow_degree (m k : ℕ) :
    ((-1 : ℤ[X]) ^ m * Polynomial.X ^ k).degree = (k : WithBot ℕ) := by
  rcases Nat.even_or_odd m with hm | hm
  · rw [hm.neg_one_pow, one_mul, Polynomial.degree_X_pow]
  · rw [hm.neg_one_pow, neg_one_mul, Polynomial.degree_neg, Polynomial.degree_X_pow]

/-! ### Section 3: Step 0 — Distinct-Partition Max-Part Bijection and Fine's Theorem -/

private def maxPartDistincts (n m : ℕ) : Finset n.Partition :=
  (Nat.Partition.distincts n).filter fun p ↦ m ∈ p.parts ∧ ∀ x ∈ p.parts, x ≤ m

private def subsetSumFinset (k m : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 k).powerset.filter fun s ↦ ∑ j ∈ s, j = m

private lemma finset_val_sum_eq (s : Finset ℕ) : s.val.sum = ∑ x ∈ s, x := by
  rw [Finset.sum, Multiset.map_id']

private lemma card_distincts_maxPart_prop (n : ℕ) (Q : ℕ → Prop) :
    ((Nat.Partition.distincts n).filter
      (fun p ↦ ∃ m ∈ p.parts, Q m ∧ ∀ x ∈ p.parts, x ≤ m)).card =
      ∑ k ∈ (Finset.range n).filter (fun k ↦ Q (k + 1)), (maxPartDistincts n (k + 1)).card := by
  have heq : (Nat.Partition.distincts n).filter
      (fun p ↦ ∃ m ∈ p.parts, Q m ∧ ∀ x ∈ p.parts, x ≤ m) =
      ((Finset.range n).filter (fun k ↦ Q (k + 1))).biUnion
        (fun k ↦ maxPartDistincts n (k + 1)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, maxPartDistincts]
    constructor
    · rintro ⟨hp, m, hm_mem, hmQ, hm_max⟩
      have hm_pos : 0 < m := p.parts_pos hm_mem
      have hm_le : m ≤ n := Nat.Partition.le_of_mem_parts hm_mem
      refine ⟨m - 1, ⟨by omega, ?_⟩, hp, ?_, ?_⟩
      · rwa [Nat.sub_add_cancel hm_pos]
      · rwa [Nat.sub_add_cancel hm_pos]
      · intro x hx
        rw [Nat.sub_add_cancel hm_pos]
        exact hm_max x hx
    · rintro ⟨k, ⟨_, hkQ⟩, hp, hm_mem, hm_max⟩
      exact ⟨hp, k + 1, hm_mem, hkQ, hm_max⟩
  rw [heq, Finset.card_biUnion]
  intro k₁ _ k₂ _ hne
  change Disjoint (maxPartDistincts n (k₁ + 1)) (maxPartDistincts n (k₂ + 1))
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  simp only [maxPartDistincts, Finset.mem_filter] at hp₁ hp₂
  have h12 : k₁ + 1 ≤ k₂ + 1 := hp₂.2.2 (k₁ + 1) hp₁.2.1
  have h21 : k₂ + 1 ≤ k₁ + 1 := hp₁.2.2 (k₂ + 1) hp₂.2.1
  omega

private lemma maxPartDistincts_card_eq_subsetSum (n k : ℕ) :
    (maxPartDistincts n (k + 1)).card =
      if k + 1 ≤ n then (subsetSumFinset k (n - (k + 1))).card else 0 := by
  split_ifs with hkn
  · symm
    refine Finset.card_bij
      (fun (s : Finset ℕ) (hs : s ∈ subsetSumFinset k (n - (k + 1))) ↦
        ({ parts := (insert (k + 1) s).val
           parts_pos := by
             intro x hx
             rw [Finset.mem_val, Finset.mem_insert] at hx
             rcases hx with rfl | hxs
             · omega
             · have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1 hxs
               rw [Finset.mem_Icc] at hsub
               omega
           parts_sum := by
             have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
             have hsum := (Finset.mem_filter.mp hs).2
             have hnot : k + 1 ∉ s := fun hc ↦ by
               have := Finset.mem_Icc.mp (hsub hc)
               omega
             rw [finset_val_sum_eq, Finset.sum_insert hnot, hsum]
             omega } : n.Partition))
      ?_ ?_ ?_
    · intro s hs
      simp only [maxPartDistincts, Finset.mem_filter, Nat.Partition.distincts, Finset.mem_univ,
        true_and]
      refine ⟨(insert (k + 1) s).nodup, Finset.mem_insert_self (k + 1) s, ?_⟩
      intro x hx
      rw [Finset.mem_val, Finset.mem_insert] at hx
      rcases hx with rfl | hxs
      · omega
      · have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1 hxs
        rw [Finset.mem_Icc] at hsub
        omega
    · intro s₁ hs₁ s₂ hs₂ heq
      have hval : (insert (k + 1) s₁).val = (insert (k + 1) s₂).val :=
        congrArg Nat.Partition.parts heq
      have hfin : insert (k + 1) s₁ = insert (k + 1) s₂ := Finset.val_inj.mp hval
      have hnot₁ : k + 1 ∉ s₁ := fun hc ↦ by
        have := Finset.mem_Icc.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hs₁).1 hc)
        omega
      have hnot₂ : k + 1 ∉ s₂ := fun hc ↦ by
        have := Finset.mem_Icc.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hs₂).1 hc)
        omega
      have herase := congrArg (fun t : Finset ℕ ↦ t.erase (k + 1)) hfin
      simpa [Finset.erase_insert hnot₁, Finset.erase_insert hnot₂] using herase
    · intro p hp
      simp only [maxPartDistincts, Finset.mem_filter, Nat.Partition.distincts, Finset.mem_univ,
        true_and] at hp
      rcases hp with ⟨hnodup, hm_mem, hm_max⟩
      refine ⟨p.parts.toFinset.erase (k + 1), ?_, ?_⟩
      · simp only [subsetSumFinset, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, ?_⟩
        · intro x hx
          rw [Finset.mem_erase, Multiset.mem_toFinset] at hx
          have hpos : 0 < x := p.parts_pos hx.2
          have hle : x ≤ k + 1 := hm_max x hx.2
          rw [Finset.mem_Icc]
          omega
        · have hmem_tf : k + 1 ∈ p.parts.toFinset := Multiset.mem_toFinset.mpr hm_mem
          have hval_eq : p.parts.toFinset.val = p.parts := by
            rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
          have htot : ∑ x ∈ p.parts.toFinset, x = n := by
            rw [← finset_val_sum_eq, hval_eq, p.parts_sum]
          have hadd := Finset.add_sum_erase p.parts.toFinset (fun x ↦ x) hmem_tf
          omega
      · ext1
        change (insert (k + 1) (p.parts.toFinset.erase (k + 1))).val = p.parts
        rw [Finset.insert_erase (Multiset.mem_toFinset.mpr hm_mem), Multiset.toFinset_val,
          Multiset.dedup_eq_self.mpr hnodup]
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [maxPartDistincts, Finset.mem_filter] at hp
    have := Nat.Partition.le_of_mem_parts hp.2.1
    omega

private lemma coeff_X_pow_mul_prod_range (n k : ℕ) :
    PowerSeries.coeff n
      ((PowerSeries.X : ℤ⟦X⟧) ^ (k + 1) *
        ∏ i ∈ Finset.range k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (i + 1))) =
      ((maxPartDistincts n (k + 1)).card : ℤ) := by
  have hprod_eq :
      (∏ i ∈ Finset.range k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (i + 1))) =
        ∏ j ∈ Finset.Icc 1 k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ j) := by
    rw [finset_Icc_one_eq_map_range, Finset.prod_map]
    rfl
  rw [hprod_eq, Finset.prod_one_add, Finset.mul_sum, map_sum]
  have hpow : ∀ t : Finset ℕ,
      (PowerSeries.X : ℤ⟦X⟧) ^ (k + 1) * (∏ j ∈ t, (PowerSeries.X : ℤ⟦X⟧) ^ j) =
        (PowerSeries.X : ℤ⟦X⟧) ^ ((k + 1) + ∑ j ∈ t, j) := by
    intro t
    rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
  simp_rw [hpow, PowerSeries.coeff_X_pow]
  rw [maxPartDistincts_card_eq_subsetSum]
  split_ifs with hkn
  · have hfilter :
        ∑ t ∈ (Finset.Icc 1 k).powerset, (if n = k + 1 + ∑ j ∈ t, j then (1 : ℤ) else 0) =
          (((Finset.Icc 1 k).powerset.filter (fun t ↦ n = k + 1 + ∑ j ∈ t, j)).card : ℤ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      split_ifs <;> simp
    rw [hfilter]
    have hset : (Finset.Icc 1 k).powerset.filter (fun t ↦ n = k + 1 + ∑ j ∈ t, j) =
        subsetSumFinset k (n - (k + 1)) := by
      ext t
      simp only [subsetSumFinset, Finset.mem_filter]
      refine and_congr_right fun _ ↦ ?_
      omega
    rw [hset]
  · refine Finset.sum_eq_zero fun t _ ↦ ?_
    have : n ≠ k + 1 + ∑ j ∈ t, j := by omega
    simp [this]

private lemma hasSum_distincts_a203568Series :
    HasSum (fun k : ℕ ↦
      (-1 : ℤ⟦X⟧) ^ k * PowerSeries.X ^ (k + 1) *
        ∏ i ∈ Finset.range k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (i + 1)))
      a203568Series := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro n
  have hfin : HasSum (fun k : ℕ ↦
      PowerSeries.coeff n ((-1 : ℤ⟦X⟧) ^ k * PowerSeries.X ^ (k + 1) *
        ∏ i ∈ Finset.range k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (i + 1))))
      (∑ k ∈ Finset.range n,
        PowerSeries.coeff n ((-1 : ℤ⟦X⟧) ^ k * PowerSeries.X ^ (k + 1) *
          ∏ i ∈ Finset.range k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (i + 1)))) := by
    refine hasSum_sum_of_ne_finset_zero fun k hk ↦ ?_
    rw [Finset.mem_range, not_lt] at hk
    have hrew : (-1 : ℤ⟦X⟧) ^ k * PowerSeries.X ^ (k + 1) *
        (∏ i ∈ Finset.range k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (i + 1))) =
        PowerSeries.X ^ (k + 1) * ((-1 : ℤ⟦X⟧) ^ k *
          ∏ i ∈ Finset.range k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (i + 1))) := by ring
    rw [hrew]
    exact coeff_X_pow_mul_eq_zero (by omega) _
  have hsum_eq : ∑ k ∈ Finset.range n,
      PowerSeries.coeff n ((-1 : ℤ⟦X⟧) ^ k * PowerSeries.X ^ (k + 1) *
        ∏ i ∈ Finset.range k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (i + 1))) =
      PowerSeries.coeff n a203568Series := by
    rw [a203568Series, PowerSeries.coeff_mk, a203568, a026837, a026838,
      card_distincts_maxPart_prop n Odd, card_distincts_maxPart_prop n Even,
      Nat.cast_sum, Nat.cast_sum]
    have hsign_coeff : ∀ k : ℕ,
        PowerSeries.coeff n ((-1 : ℤ⟦X⟧) ^ k * PowerSeries.X ^ (k + 1) *
          ∏ i ∈ Finset.range k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (i + 1))) =
        (-1 : ℤ) ^ k * ((maxPartDistincts n (k + 1)).card : ℤ) := by
      intro k
      rcases Nat.even_or_odd k with hk | hk
      · rw [hk.neg_one_pow, hk.neg_one_pow, one_mul, one_mul, coeff_X_pow_mul_prod_range]
      · rw [hk.neg_one_pow, hk.neg_one_pow, neg_one_mul, neg_one_mul, neg_mul, map_neg,
          coeff_X_pow_mul_prod_range]
    simp_rw [hsign_coeff]
    have hpart := (Finset.sum_filter_add_sum_filter_not (Finset.range n)
      (fun k ↦ Odd (k + 1))
      (fun k ↦ (-1 : ℤ) ^ k * ((maxPartDistincts n (k + 1)).card : ℤ))).symm
    rw [hpart]
    have hodd_sum :
        ∑ k ∈ (Finset.range n).filter (fun k ↦ Odd (k + 1)),
          (-1 : ℤ) ^ k * ((maxPartDistincts n (k + 1)).card : ℤ) =
        ∑ k ∈ (Finset.range n).filter (fun k ↦ Odd (k + 1)),
          ((maxPartDistincts n (k + 1)).card : ℤ) := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_filter] at hk
      have hev : Even k := by
        rcases Nat.even_or_odd k with h | h
        · exact h
        · exfalso
          have h1 : Even (k + 1) := h.add_odd odd_one
          exact (Nat.not_odd_iff_even.mpr h1) hk.2
      rw [hev.neg_one_pow, one_mul]
    have heven_filter :
        (Finset.range n).filter (fun k ↦ ¬ Odd (k + 1)) =
          (Finset.range n).filter (fun k ↦ Even (k + 1)) := by
      ext k
      simp [Nat.not_odd_iff_even]
    have heven_sum :
        ∑ k ∈ (Finset.range n).filter (fun k ↦ Even (k + 1)),
          (-1 : ℤ) ^ k * ((maxPartDistincts n (k + 1)).card : ℤ) =
        -(∑ k ∈ (Finset.range n).filter (fun k ↦ Even (k + 1)),
          ((maxPartDistincts n (k + 1)).card : ℤ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_filter] at hk
      have hodd : Odd k := by
        rcases Nat.even_or_odd k with h | h
        · exfalso
          have h1 : Odd (k + 1) := h.add_odd odd_one
          exact (Nat.not_even_iff_odd.mpr h1) hk.2
        · exact h
      rw [hodd.neg_one_pow, neg_one_mul]
    rw [hodd_sum, heven_filter, heven_sum, ← sub_eq_add_neg]
    congr 1 <;> refine Finset.sum_congr (by ext x; simp) fun _ _ ↦ rfl
  rwa [hsum_eq] at hfin

private lemma pentagonal_nat_succ (k : ℕ) :
    pentagonal ((k : ℤ) + 1) = (k + 1) * (3 * k + 2) / 2 := by
  grind [pentagonal_def]

private lemma pentagonal_succ_step (k : ℕ) :
    pentagonal ((k : ℤ) + 1) + (3 * k + 4) = pentagonal ((k : ℤ) + 2) := by
  have h1 := two_mul_natCast_pentagonal ((k : ℤ) + 1)
  have h2 := two_mul_natCast_pentagonal ((k : ℤ) + 2)
  have hlin : (pentagonal ((k : ℤ) + 1) : ℤ) + (3 * (k : ℤ) + 4) =
      (pentagonal ((k : ℤ) + 2) : ℤ) := by
    linarith
  exact_mod_cast hlin

private lemma pentagonal_neg_eq_add_succ (k : ℕ) :
    pentagonal (-((k : ℤ) + 1)) = pentagonal ((k : ℤ) + 1) + (k + 1) := by
  have h1 := two_mul_natCast_pentagonal ((k : ℤ) + 1)
  have h2 := two_mul_natCast_pentagonal (-((k : ℤ) + 1))
  have hlin : (pentagonal (-((k : ℤ) + 1)) : ℤ) =
      (pentagonal ((k : ℤ) + 1) : ℤ) + ((k : ℤ) + 1) := by
    linarith
  exact_mod_cast hlin

private def step0Summand (k m : ℕ) : ℤ⟦X⟧ :=
  (-1 : ℤ⟦X⟧) ^ m *
    (PowerSeries.X : ℤ⟦X⟧) ^ (pentagonal ((k : ℤ) + 1) + (k + 1) * m) *
    ∏ i ∈ Finset.range m, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 1 + i))

private def step0Aux (k r : ℕ) : ℤ⟦X⟧ :=
  (-1 : ℤ⟦X⟧) ^ r *
    (PowerSeries.X : ℤ⟦X⟧) ^ (pentagonal ((k : ℤ) + 1) + (k + 1) * (r + 2)) *
    ∏ i ∈ Finset.range r, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 2 + i))

private lemma step0Summand_vanish (k d m : ℕ) (hm : d + 1 ≤ m) :
    PowerSeries.coeff d (step0Summand k m) = 0 := by
  unfold step0Summand
  have he : d < pentagonal ((k : ℤ) + 1) + (k + 1) * m := by
    have : m ≤ (k + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    omega
  have hrew : (-1 : ℤ⟦X⟧) ^ m *
      (PowerSeries.X : ℤ⟦X⟧) ^ (pentagonal ((k : ℤ) + 1) + (k + 1) * m) *
      (∏ i ∈ Finset.range m, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 1 + i))) =
      (PowerSeries.X : ℤ⟦X⟧) ^ (pentagonal ((k : ℤ) + 1) + (k + 1) * m) *
      ((-1 : ℤ⟦X⟧) ^ m * ∏ i ∈ Finset.range m, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 1 + i))) := by
    ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero he _

private def step0Rem (k : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun d ↦ ∑ m ∈ Finset.range (d + 1), PowerSeries.coeff d (step0Summand k m)

private lemma hasSum_step0Summand (k : ℕ) : HasSum (step0Summand k) (step0Rem k) :=
  hasSum_mk_of_coeff_vanish (step0Summand k) (fun d ↦ d + 1) (step0Summand_vanish k)

private lemma step0Rem_zero_eq_a203568Series : step0Rem 0 = a203568Series := by
  have h0 := hasSum_step0Summand 0
  have h1 := hasSum_distincts_a203568Series
  have hp1 : pentagonal (1 : ℤ) = 1 := by decide
  have heq : step0Summand 0 = fun m : ℕ ↦
      (-1 : ℤ⟦X⟧) ^ m * PowerSeries.X ^ (m + 1) *
        ∏ i ∈ Finset.range m, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (i + 1)) := by
    ext m
    simp only [step0Summand, Int.ofNat_zero, zero_add, hp1, one_mul, Nat.add_comm 1 m]
    congr 2
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Nat.add_comm 1 i]
  rw [heq] at h0
  exact h0.unique h1

private lemma step0_telescoping_term (k r : ℕ) :
    step0Summand k (r + 2) - step0Summand (k + 1) r =
      step0Aux k r - step0Aux k (r + 1) := by
  unfold step0Summand step0Aux
  rw [Finset.prod_range_succ' _ (r + 1)]
  have hshift : (∏ x ∈ Finset.range (r + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 1 + (x + 1)))) =
      (∏ i ∈ Finset.range r, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 2 + i))) *
        (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 2 + r)) := by
    rw [← Finset.prod_range_succ]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    congr 2
    omega
  have hshift2 : (∏ i ∈ Finset.range r, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 1 + 1 + i))) =
      ∏ i ∈ Finset.range r, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 2 + i)) := rfl
  rw [hshift, hshift2, Finset.prod_range_succ]
  have hp_step : pentagonal (((k + 1 : ℕ) : ℤ) + 1) =
      pentagonal ((k : ℤ) + 1) + (3 * k + 4) := by
    simpa [Nat.cast_add, add_assoc] using (pentagonal_succ_step k).symm
  have hexp1 : pentagonal (((k + 1 : ℕ) : ℤ) + 1) + (k + 1 + 1) * r =
      (pentagonal ((k : ℤ) + 1) + (k + 1) * (r + 2)) + (k + 2 + r) := by
    rw [hp_step]
    ring
  have hexp2 : pentagonal ((k : ℤ) + 1) + (k + 1) * (r + 1 + 2) =
      (pentagonal ((k : ℤ) + 1) + (k + 1) * (r + 2)) + (k + 1) := by
    ring
  rw [hexp1, hexp2]
  have hpow0 : (PowerSeries.X : ℤ⟦X⟧) ^ (k + 1 + 0) = (PowerSeries.X : ℤ⟦X⟧) ^ (k + 1) := by
    rw [Nat.add_zero]
  rw [hpow0]
  simp only [pow_add, pow_two, pow_one]
  ring

private lemma step0Rem_sub_succ (k : ℕ) :
    step0Rem k - step0Rem (k + 1) =
      (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 1) -
        (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-((k : ℤ) + 1)) := by
  have haux_sum : HasSum (fun r ↦ step0Summand k (r + 2) - step0Summand (k + 1) r)
      (step0Aux k 0) := by
    refine hasSum_of_sub_eq_and_coeff_zero (step0Aux k) _
      (fun r ↦ (step0_telescoping_term k r).symm) ?_
    intro d r hdr
    unfold step0Aux
    have he : d < pentagonal ((k : ℤ) + 1) + (k + 1) * (r + 2) := by
      have : r + 2 ≤ (k + 1) * (r + 2) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hrew : (-1 : ℤ⟦X⟧) ^ r *
        (PowerSeries.X : ℤ⟦X⟧) ^ (pentagonal ((k : ℤ) + 1) + (k + 1) * (r + 2)) *
        (∏ i ∈ Finset.range r, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 2 + i))) =
        (PowerSeries.X : ℤ⟦X⟧) ^ (pentagonal ((k : ℤ) + 1) + (k + 1) * (r + 2)) *
        ((-1 : ℤ⟦X⟧) ^ r * ∏ i ∈ Finset.range r, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 2 + i))) := by
      ring
    rw [hrew]
    exact coeff_X_pow_mul_eq_zero he _
  have hshift2 : HasSum (fun r ↦ step0Summand k (r + 2))
      (step0Rem k - step0Summand k 0 - step0Summand k 1) := by
    have hk_all := hasSum_step0Summand k
    rw [← hasSum_nat_add_iff' 2] at hk_all
    convert hk_all using 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    ring
  have hdiff := hshift2.sub (hasSum_step0Summand (k + 1))
  have heq := hdiff.unique haux_sum
  have h01 : step0Summand k 0 + step0Summand k 1 + step0Aux k 0 =
      (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 1) -
        (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-((k : ℤ) + 1)) := by
    unfold step0Summand step0Aux
    rw [pentagonal_neg_eq_add_succ k]
    simp only [Finset.prod_range_zero, Finset.prod_range_one, mul_zero, mul_one,
      Nat.add_zero, pow_zero, pow_one]
    have hexp : pentagonal ((k : ℤ) + 1) + (k + 1) * 2 =
        (pentagonal ((k : ℤ) + 1) + (k + 1)) + (k + 1) := by ring
    rw [hexp]
    simp only [pow_add]
    ring
  calc
    step0Rem k - step0Rem (k + 1)
        = (step0Rem k - step0Summand k 0 - step0Summand k 1 - step0Rem (k + 1)) +
            (step0Summand k 0 + step0Summand k 1) := by ring
    _ = step0Aux k 0 + (step0Summand k 0 + step0Summand k 1) := by rw [heq]
    _ = step0Summand k 0 + step0Summand k 1 + step0Aux k 0 := by ring
    _ = (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 1) -
          (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-((k : ℤ) + 1)) := h01

private lemma step0Rem_coeff_zero {d k : ℕ} (hdk : d < k) :
    PowerSeries.coeff d (step0Rem k) = 0 := by
  rw [step0Rem, PowerSeries.coeff_mk]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  unfold step0Summand
  have hp : k + 1 ≤ pentagonal ((k : ℤ) + 1) := by
    rw [pentagonal_nat_succ]
    have hmul : (k + 1) * 2 ≤ (k + 1) * (3 * k + 2) :=
      Nat.mul_le_mul_left (k + 1) (show 2 ≤ 3 * k + 2 by omega)
    omega
  have he : d < pentagonal ((k : ℤ) + 1) + (k + 1) * m := by omega
  have hrew : (-1 : ℤ⟦X⟧) ^ m *
      (PowerSeries.X : ℤ⟦X⟧) ^ (pentagonal ((k : ℤ) + 1) + (k + 1) * m) *
      (∏ i ∈ Finset.range m, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 1 + i))) =
      (PowerSeries.X : ℤ⟦X⟧) ^ (pentagonal ((k : ℤ) + 1) + (k + 1) * m) *
      ((-1 : ℤ⟦X⟧) ^ m * ∏ i ∈ Finset.range m, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (k + 1 + i))) := by
    ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero he _

private lemma hasSum_pentagonal_a203568Series :
    HasSum (fun k : ℕ ↦
      (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 1) -
        (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-((k : ℤ) + 1)))
      a203568Series := by
  rw [← step0Rem_zero_eq_a203568Series]
  exact hasSum_of_sub_eq_and_coeff_zero step0Rem _ step0Rem_sub_succ
    (fun d M h ↦ step0Rem_coeff_zero h)

/-! ### Section 4: Links 1 & 2 — Somos's Alternating Series and Ramanujan's Entry 9.4.4 -/

private def link1Exp (M r : ℕ) : ℕ :=
  (M + r) * (M + r + 1) / 2 + M ^ 2 + M * r

private def link1Prod (M r : ℕ) : ℤ⟦X⟧ :=
  ∏ i ∈ Finset.range r, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (M + 1 + i))

private lemma link1Prod_const (M r : ℕ) :
    PowerSeries.constantCoeff (link1Prod M r) = 1 :=
  constantCoeff_prod_one_add _ _ (fun _ _ ↦ by omega)

private lemma link1Prod_succ_right (M r : ℕ) :
    link1Prod M (r + 1) = link1Prod M r * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (M + 1 + r)) :=
  Finset.prod_range_succ _ r

private lemma link1Prod_succ_left (M s : ℕ) :
    link1Prod M (s + 1) = (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (M + 1)) * link1Prod (M + 1) s := by
  unfold link1Prod
  rw [Finset.prod_range_succ', mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [Nat.add_zero]
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    have : M + 1 + (i + 1) = M + 1 + 1 + i := by omega
    rw [this]

private lemma tri_succ (K : ℕ) :
    (K + 1) * (K + 2) / 2 = K * (K + 1) / 2 + (K + 1) := by
  have h : (K + 1) * (K + 2) = K * (K + 1) + (K + 1) * 2 := by ring
  rw [h, Nat.add_mul_div_right _ _ (by omega)]

private lemma link1Exp_succ_left (M s : ℕ) :
    link1Exp (M + 1) s = link1Exp M (s + 1) + (M + s + 1) := by
  unfold link1Exp
  have h1 : M + 1 + s = M + (s + 1) := by omega
  rw [h1]
  ring

private lemma link1Exp_succ_right (M u : ℕ) :
    link1Exp M (u + 1) = link1Exp M u + (2 * M + u + 1) := by
  unfold link1Exp
  have h1 : M + (u + 1) = (M + u) + 1 := by omega
  have h2 : (M + u + 1) + 1 = (M + u) + 2 := by omega
  rw [h1, h2, tri_succ (M + u)]
  ring

private lemma link1Exp_zero_eq_pentagonal_neg (M : ℕ) :
    link1Exp M 0 = pentagonal (-(M : ℤ)) := by
  unfold link1Exp
  simp only [Nat.add_zero, mul_zero]
  have hp := two_mul_natCast_pentagonal (-(M : ℤ))
  have htri : 2 * (M * (M + 1) / 2) = M * (M + 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_succ_self M).two_dvd
  have hlin : 2 * ((M * (M + 1) / 2 + M ^ 2 : ℕ) : ℤ) = 2 * (pentagonal (-(M : ℤ)) : ℤ) := by
    push_cast
    have htriZ : (2 : ℤ) * ((M * (M + 1) / 2 : ℕ) : ℤ) = (M : ℤ) * ((M : ℤ) + 1) := by
      exact_mod_cast htri
    linarith
  omega

private lemma link1Exp_one_eq_pentagonal_succ (M : ℕ) :
    link1Exp M 1 = pentagonal ((M : ℤ) + 1) := by
  rw [link1Exp_succ_right M 0, link1Exp_zero_eq_pentagonal_neg M]
  have hp1 := two_mul_natCast_pentagonal (-(M : ℤ))
  have hp2 := two_mul_natCast_pentagonal ((M : ℤ) + 1)
  have hlin : (pentagonal (-(M : ℤ)) : ℤ) + (2 * (M : ℤ) + 1) =
      (pentagonal ((M : ℤ) + 1) : ℤ) := by
    linarith
  exact_mod_cast hlin

private def link1Summand (M r : ℕ) : ℤ⟦X⟧ :=
  (-1 : ℤ⟦X⟧) ^ r * (PowerSeries.X : ℤ⟦X⟧) ^ link1Exp M r * inv1 (link1Prod M r)

private def link1Aux (M s : ℕ) : ℤ⟦X⟧ :=
  (-1 : ℤ⟦X⟧) ^ (s + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ link1Exp M (s + 1) * inv1 (link1Prod M s)

private lemma link1_ge_add (M r : ℕ) : M + r ≤ link1Exp M r := by
  induction r with
  | zero =>
    unfold link1Exp
    have hsq : M ≤ M ^ 2 := Nat.le_self_pow (by omega) M
    omega
  | succ r ih =>
    rw [link1Exp_succ_right]
    omega

private lemma link1Summand_vanish (M d r : ℕ) (hr : d + 1 ≤ r) :
    PowerSeries.coeff d (link1Summand M r) = 0 := by
  unfold link1Summand
  have he : d < link1Exp M r := by
    have := link1_ge_add M r
    omega
  have hrew : (-1 : ℤ⟦X⟧) ^ r * (PowerSeries.X : ℤ⟦X⟧) ^ link1Exp M r * inv1 (link1Prod M r) =
      (PowerSeries.X : ℤ⟦X⟧) ^ link1Exp M r * ((-1 : ℤ⟦X⟧) ^ r * inv1 (link1Prod M r)) := by
    ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero he _

private def link1Rem (M : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun d ↦ ∑ r ∈ Finset.range (d + 1), PowerSeries.coeff d (link1Summand M r)

private lemma hasSum_link1Summand (M : ℕ) : HasSum (link1Summand M) (link1Rem M) :=
  hasSum_mk_of_coeff_vanish (link1Summand M) (fun d ↦ d + 1) (link1Summand_vanish M)

private lemma link1_telescoping_term (M s : ℕ) :
    link1Summand M (s + 1) - link1Summand (M + 1) s =
      link1Aux M s - link1Aux M (s + 1) := by
  unfold link1Summand link1Aux
  have hinv_left : inv1 (link1Prod (M + 1) s) =
      (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (M + 1)) * inv1 (link1Prod M (s + 1)) := by
    rw [link1Prod_succ_left M s]
    exact (mul_inv1_cancel_left (constantCoeff_one_add_X_pow (by omega))
      (link1Prod_const (M + 1) s)).symm
  have hinv_right : inv1 (link1Prod M s) =
      (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (M + 1 + s)) * inv1 (link1Prod M (s + 1)) := by
    rw [link1Prod_succ_right M s]
    exact (mul_inv1_cancel_right (link1Prod_const M s)
      (constantCoeff_one_add_X_pow (by omega))).symm
  rw [hinv_left, hinv_right, link1Exp_succ_left M s, link1Exp_succ_right M (s + 1)]
  have h2m : 2 * M + (s + 1) + 1 = (M + s + 1) + (M + 1) := by omega
  have h1s : M + 1 + s = M + s + 1 := by omega
  rw [h2m, h1s]
  simp only [pow_add, pow_one]
  ring

private lemma link1Rem_sub_succ (M : ℕ) :
    link1Rem M - link1Rem (M + 1) =
      (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-(M : ℤ)) -
        (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((M : ℤ) + 1) := by
  have haux_sum : HasSum (fun s ↦ link1Summand M (s + 1) - link1Summand (M + 1) s)
      (link1Aux M 0) := by
    refine hasSum_of_sub_eq_and_coeff_zero (link1Aux M) _
      (fun s ↦ (link1_telescoping_term M s).symm) ?_
    intro d s hds
    unfold link1Aux
    have he : d < link1Exp M (s + 1) := by
      have := link1_ge_add M (s + 1)
      omega
    have hrew : (-1 : ℤ⟦X⟧) ^ (s + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ link1Exp M (s + 1) *
        inv1 (link1Prod M s) =
        (PowerSeries.X : ℤ⟦X⟧) ^ link1Exp M (s + 1) *
          ((-1 : ℤ⟦X⟧) ^ (s + 1) * inv1 (link1Prod M s)) := by ring
    rw [hrew]
    exact coeff_X_pow_mul_eq_zero he _
  have hshift1 : HasSum (fun s ↦ link1Summand M (s + 1)) (link1Rem M - link1Summand M 0) := by
    have hM := hasSum_link1Summand M
    rw [← hasSum_nat_add_iff' 1] at hM
    simpa [Finset.sum_range_one] using hM
  have heq := (hshift1.sub (hasSum_link1Summand (M + 1))).unique haux_sum
  have h0 : link1Summand M 0 + link1Aux M 0 =
      (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-(M : ℤ)) -
        (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((M : ℤ) + 1) := by
    unfold link1Summand link1Aux
    simp only [link1Prod, Finset.prod_range_zero, inv1_one, mul_one, pow_zero, one_mul]
    rw [link1Exp_zero_eq_pentagonal_neg M, link1Exp_one_eq_pentagonal_succ M]
    ring
  calc
    link1Rem M - link1Rem (M + 1)
        = (link1Rem M - link1Summand M 0 - link1Rem (M + 1)) + link1Summand M 0 := by ring
    _ = link1Aux M 0 + link1Summand M 0 := by rw [heq]
    _ = link1Summand M 0 + link1Aux M 0 := by ring
    _ = (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-(M : ℤ)) -
          (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((M : ℤ) + 1) := h0

private lemma link1Rem_coeff_zero {d M : ℕ} (hdM : d < M) :
    PowerSeries.coeff d (link1Rem M) = 0 := by
  rw [link1Rem, PowerSeries.coeff_mk]
  refine Finset.sum_eq_zero fun r _ ↦ ?_
  unfold link1Summand
  have he : d < link1Exp M r := by
    have := link1_ge_add M r
    omega
  have hrew : (-1 : ℤ⟦X⟧) ^ r * (PowerSeries.X : ℤ⟦X⟧) ^ link1Exp M r * inv1 (link1Prod M r) =
      (PowerSeries.X : ℤ⟦X⟧) ^ link1Exp M r * ((-1 : ℤ⟦X⟧) ^ r * inv1 (link1Prod M r)) := by ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero he _

private lemma link1Rem_zero_eq_one_sub_a203568Series :
    link1Rem 0 = 1 - a203568Series := by
  have hL0 : HasSum (fun M : ℕ ↦
      (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-(M : ℤ)) -
        (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((M : ℤ) + 1)) (link1Rem 0) :=
    hasSum_of_sub_eq_and_coeff_zero link1Rem _ link1Rem_sub_succ
      (fun d M h ↦ link1Rem_coeff_zero h)
  have hL0_shift : HasSum (fun k : ℕ ↦
      (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-((k : ℤ) + 1)) -
        (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 2))
      (link1Rem 0 - (1 - PowerSeries.X)) := by
    rw [← hasSum_nat_add_iff' 1] at hL0
    have hp0 : pentagonal (0 : ℤ) = 0 := rfl
    have hp1 : pentagonal (1 : ℤ) = 1 := by decide
    convert hL0 using 1
    · funext k
      simp [Nat.cast_add, add_assoc]
    · simp [hp0, hp1]
  have hA_shift : HasSum (fun k : ℕ ↦
      (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-((k : ℤ) + 1)) -
        (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 2))
      (1 - a203568Series - (1 - PowerSeries.X)) := by
    have hcomb : ∀ k : ℕ,
        ((PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-((k : ℤ) + 1)) -
          (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 2)) =
        (((PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 1) -
          (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 2)) -
          ((PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 1) -
            (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-((k : ℤ) + 1)))) := by
      intro k
      ring
    have htel0 : HasSum (fun k : ℕ ↦
        (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 1) -
          (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 2))
        ((PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((0 : ℤ) + 1)) := by
      refine hasSum_of_sub_eq_and_coeff_zero
        (fun k : ℕ ↦ (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 1)) _
        (fun k ↦ by simp [Nat.cast_add, add_assoc]) ?_
      intro d k hdk
      have hp_ge : k + 1 ≤ pentagonal ((k : ℤ) + 1) := by
        rw [pentagonal_nat_succ]
        have hmul : (k + 1) * 2 ≤ (k + 1) * (3 * k + 2) :=
          Nat.mul_le_mul_left (k + 1) (show 2 ≤ 3 * k + 2 by omega)
        omega
      rw [PowerSeries.coeff_X_pow]
      have : d ≠ pentagonal ((k : ℤ) + 1) := by omega
      simp [this]
    have hp1 : (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((0 : ℤ) + 1) = PowerSeries.X := by
      have : pentagonal (1 : ℤ) = 1 := by decide
      simp [this]
    rw [hp1] at htel0
    have hsub := htel0.sub hasSum_pentagonal_a203568Series
    convert hsub using 1
    · funext k
      exact hcomb k
    · ring
  have heq := hL0_shift.unique hA_shift
  calc
    link1Rem 0 = (link1Rem 0 - (1 - PowerSeries.X)) + (1 - PowerSeries.X) := by ring
    _ = (1 - a203568Series - (1 - PowerSeries.X)) + (1 - PowerSeries.X) := by rw [heq]
    _ = 1 - a203568Series := by ring

private def somosTerm (m : ℕ) : ℤ⟦X⟧ :=
  (-1 : ℤ⟦X⟧) ^ m * (PowerSeries.X : ℤ⟦X⟧) ^ ((m + 1) * (m + 2) / 2) *
    inv1 (link1Prod 0 (m + 1))

private lemma hasSum_somos_a203568Series : HasSum somosTerm a203568Series := by
  have hL0 := hasSum_link1Summand 0
  rw [link1Rem_zero_eq_one_sub_a203568Series, ← hasSum_nat_add_iff' 1] at hL0
  have h0 : link1Summand 0 0 = 1 := by
    simp [link1Summand, link1Exp, link1Prod, inv1_one]
  rw [Finset.sum_range_one, h0] at hL0
  have hneg := hL0.neg
  convert hneg using 1
  · funext m
    unfold somosTerm link1Summand link1Exp
    simp only [zero_add, zero_pow (by omega : 2 ≠ 0), zero_mul, Nat.add_zero, pow_add, pow_one]
    ring
  · ring

private lemma hasSum_entry944_a203568Series :
    HasSum (fun k : ℕ ↦
      (PowerSeries.X : ℤ⟦X⟧) ^ ((k + 1) * (2 * k + 1)) * inv1 (link1Prod 0 (2 * k + 2)))
      a203568Series := by
  have he : ∃ Se : ℤ⟦X⟧, HasSum (fun k : ℕ ↦ somosTerm (2 * k)) Se := by
    refine ⟨_, hasSum_mk_of_coeff_vanish (fun k ↦ somosTerm (2 * k)) (fun d ↦ d + 1) ?_⟩
    intro d k hk
    unfold somosTerm
    have hexp : d < (2 * k + 1) * (2 * k + 2) / 2 := by
      have hmul : (2 * k + 1) * 2 ≤ (2 * k + 1) * (2 * k + 2) :=
        Nat.mul_le_mul_left (2 * k + 1) (show 2 ≤ 2 * k + 2 by omega)
      omega
    have hrew : (-1 : ℤ⟦X⟧) ^ (2 * k) *
        (PowerSeries.X : ℤ⟦X⟧) ^ ((2 * k + 1) * (2 * k + 2) / 2) *
        inv1 (link1Prod 0 (2 * k + 1)) =
        (PowerSeries.X : ℤ⟦X⟧) ^ ((2 * k + 1) * (2 * k + 2) / 2) *
          ((-1 : ℤ⟦X⟧) ^ (2 * k) * inv1 (link1Prod 0 (2 * k + 1))) := by ring
    rw [hrew]
    exact coeff_X_pow_mul_eq_zero hexp _
  have ho : ∃ So : ℤ⟦X⟧, HasSum (fun k : ℕ ↦ somosTerm (2 * k + 1)) So := by
    refine ⟨_, hasSum_mk_of_coeff_vanish (fun k ↦ somosTerm (2 * k + 1)) (fun d ↦ d + 1) ?_⟩
    intro d k hk
    unfold somosTerm
    have hexp : d < (2 * k + 1 + 1) * (2 * k + 1 + 2) / 2 := by
      have hmul : 2 * (2 * k + 2) ≤ (2 * k + 1 + 1) * (2 * k + 1 + 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    have hrew : (-1 : ℤ⟦X⟧) ^ (2 * k + 1) *
        (PowerSeries.X : ℤ⟦X⟧) ^ ((2 * k + 1 + 1) * (2 * k + 1 + 2) / 2) *
        inv1 (link1Prod 0 (2 * k + 1 + 1)) =
        (PowerSeries.X : ℤ⟦X⟧) ^ ((2 * k + 1 + 1) * (2 * k + 1 + 2) / 2) *
          ((-1 : ℤ⟦X⟧) ^ (2 * k + 1) * inv1 (link1Prod 0 (2 * k + 1 + 1))) := by ring
    rw [hrew]
    exact coeff_X_pow_mul_eq_zero hexp _
  rcases he with ⟨Se, hSe⟩
  rcases ho with ⟨So, hSo⟩
  have htot := (hSe.even_add_odd hSo).unique hasSum_somos_a203568Series
  have hpair := hSe.add hSo
  rw [htot] at hpair
  refine hpair.congr_fun fun k ↦ ?_
  unfold somosTerm
  have hev : Even (2 * k) := even_two_mul k
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have htri1 : (2 * k + 1) * (2 * k + 2) / 2 = (k + 1) * (2 * k + 1) := by
    have : (2 * k + 1) * (2 * k + 2) = ((k + 1) * (2 * k + 1)) * 2 := by ring
    rw [this, Nat.mul_div_cancel _ (by omega)]
  have htri2 : (2 * k + 1 + 1) * (2 * k + 1 + 2) / 2 = (k + 1) * (2 * k + 1) + (2 * k + 2) := by
    have : (2 * k + 1 + 1) * (2 * k + 1 + 2) =
        ((k + 1) * (2 * k + 1) + (2 * k + 2)) * 2 := by ring
    rw [this, Nat.mul_div_cancel _ (by omega)]
  have hinv : inv1 (link1Prod 0 (2 * k + 1)) =
      (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k + 2)) * inv1 (link1Prod 0 (2 * k + 2)) := by
    have hpr : link1Prod 0 (2 * k + 2) =
        link1Prod 0 (2 * k + 1) * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k + 2)) := by
      simpa [Nat.zero_add, Nat.add_comm 1 (2 * k + 1)] using link1Prod_succ_right 0 (2 * k + 1)
    rw [hpr]
    exact (mul_inv1_cancel_right (link1Prod_const 0 (2 * k + 1))
      (constantCoeff_one_add_X_pow (by omega))).symm
  rw [hev.neg_one_pow, hodd.neg_one_pow, htri1, htri2, pow_add]
  have h2k : 2 * k + 1 + 1 = 2 * k + 2 := by omega
  rw [h2k, hinv]
  ring

/-! ### Section 5: Link 3 — Corrected Rogers–Fine Specialization (`C036`, `N = 1`) -/

private def rfOddProd (k : ℕ) : ℤ⟦X⟧ :=
  ∏ i ∈ Finset.range k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * i + 3))

private def rfEvenProd (M : ℕ) : ℤ⟦X⟧ :=
  ∏ i ∈ Finset.range M, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * i + 2))

private lemma rfOddProd_const (k : ℕ) : PowerSeries.constantCoeff (rfOddProd k) = 1 :=
  constantCoeff_prod_one_add _ _ (fun _ _ ↦ by omega)

private lemma rfEvenProd_const (M : ℕ) : PowerSeries.constantCoeff (rfEvenProd M) = 1 :=
  constantCoeff_prod_one_add _ _ (fun _ _ ↦ by omega)

private def rfExp (M r : ℕ) : ℕ :=
  5 * M + 2 * r + 2 * (M * (M - 1) + M * r)

private lemma rfExp_shift_r (M s : ℕ) :
    (2 * M + 2) + rfExp M s = rfExp M (s + 1) := by
  unfold rfExp
  ring

private lemma rfExp_step_M (M s : ℕ) :
    rfExp M (s + 1) + (2 * M + 2 * s + 3) = rfExp (M + 1) s := by
  unfold rfExp
  cases M with
  | zero => ring
  | succ m =>
    simp only [Nat.add_sub_cancel]
    ring

private lemma one_add_rfExp_zero (m : ℕ) :
    1 + rfExp m 0 = (m + 1) * (2 * m + 1) := by
  unfold rfExp
  cases m with
  | zero => rfl
  | succ k =>
    simp only [Nat.add_sub_cancel]
    ring

private def rfSummand (M r : ℕ) : ℤ⟦X⟧ :=
  (-1 : ℤ⟦X⟧) ^ r * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M r *
    inv1 (rfOddProd (M + r)) * inv1 (rfEvenProd M)

private lemma rfSummand_vanish (M d r : ℕ) (hr : d + 1 ≤ r) :
    PowerSeries.coeff d (rfSummand M r) = 0 := by
  unfold rfSummand
  have he : d < rfExp M r := by
    unfold rfExp
    omega
  have hrew : (-1 : ℤ⟦X⟧) ^ r * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M r *
      inv1 (rfOddProd (M + r)) * inv1 (rfEvenProd M) =
      (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M r *
        ((-1 : ℤ⟦X⟧) ^ r * inv1 (rfOddProd (M + r)) * inv1 (rfEvenProd M)) := by ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero he _

private def rfRem (M : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun d ↦ ∑ r ∈ Finset.range (d + 1), PowerSeries.coeff d (rfSummand M r)

private lemma hasSum_rfSummand (M : ℕ) : HasSum (rfSummand M) (rfRem M) :=
  hasSum_mk_of_coeff_vanish (rfSummand M) (fun d ↦ d + 1) (rfSummand_vanish M)

private lemma rf_term_identity (M s : ℕ) :
    rfSummand M (s + 1) + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2) * rfSummand M s =
      (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) * rfSummand (M + 1) s := by
  unfold rfSummand
  have hodd_step : inv1 (rfOddProd (M + s)) =
      (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * (M + s) + 3)) * inv1 (rfOddProd (M + s + 1)) := by
    have hpr : rfOddProd (M + s + 1) =
        rfOddProd (M + s) * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * (M + s) + 3)) :=
      Finset.prod_range_succ _ (M + s)
    rw [hpr]
    exact (mul_inv1_cancel_right (rfOddProd_const (M + s))
      (constantCoeff_one_add_X_pow (by omega))).symm
  have heven_step : (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) * inv1 (rfEvenProd (M + 1)) =
      inv1 (rfEvenProd M) := by
    have hpr : rfEvenProd (M + 1) =
        rfEvenProd M * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) :=
      Finset.prod_range_succ _ M
    rw [hpr]
    exact mul_inv1_cancel_right (rfEvenProd_const M)
      (constantCoeff_one_add_X_pow (by omega))
  have hMs : M + (s + 1) = M + s + 1 := by omega
  have hM1s : M + 1 + s = M + s + 1 := by omega
  rw [hMs, hM1s, hodd_step]
  have hrhs : (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) *
      ((-1 : ℤ⟦X⟧) ^ s * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp (M + 1) s *
        inv1 (rfOddProd (M + s + 1)) * inv1 (rfEvenProd (M + 1))) =
      (-1 : ℤ⟦X⟧) ^ s * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp (M + 1) s *
        inv1 (rfOddProd (M + s + 1)) *
        ((1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) * inv1 (rfEvenProd (M + 1))) := by ring
  rw [hrhs, heven_step, ← rfExp_step_M M s]
  have hlhs_exp : (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2) *
      ((-1 : ℤ⟦X⟧) ^ s * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M s *
        ((1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * (M + s) + 3)) * inv1 (rfOddProd (M + s + 1))) *
        inv1 (rfEvenProd M)) =
      (-1 : ℤ⟦X⟧) ^ s * ((PowerSeries.X : ℤ⟦X⟧) ^ ((2 * M + 2) + rfExp M s)) *
        (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2 * s + 3)) *
        inv1 (rfOddProd (M + s + 1)) * inv1 (rfEvenProd M) := by
    rw [pow_add]
    have : 2 * (M + s) + 3 = 2 * M + 2 * s + 3 := by omega
    rw [this]
    ring
  rw [hlhs_exp, rfExp_shift_r M s]
  simp only [pow_add, pow_one]
  ring

private lemma rfRem_sub_succ (M : ℕ) :
    rfRem M - rfRem (M + 1) =
      (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M 0 * inv1 (rfOddProd M) * inv1 (rfEvenProd (M + 1)) := by
  have hshift : HasSum (fun s ↦ rfSummand M (s + 1)) (rfRem M - rfSummand M 0) := by
    have hM := hasSum_rfSummand M
    rw [← hasSum_nat_add_iff' 1] at hM
    simpa [Finset.sum_range_one] using hM
  have hmul := (hasSum_rfSummand M).mul_left ((PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2))
  have hsum_lhs := hshift.add hmul
  have hsum_rhs := (hasSum_rfSummand (M + 1)).mul_left (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2))
  have hcongr : (fun s ↦ rfSummand M (s + 1) + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2) * rfSummand M s) =
      (fun s ↦ (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) * rfSummand (M + 1) s) := by
    funext s
    exact rf_term_identity M s
  rw [hcongr] at hsum_lhs
  have heq := hsum_lhs.unique hsum_rhs
  have hunit : (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) * (rfRem M - rfRem (M + 1)) =
      rfSummand M 0 := by
    calc
      (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) * (rfRem M - rfRem (M + 1))
          = (rfRem M - rfSummand M 0 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2) * rfRem M) -
              (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) * rfRem (M + 1) + rfSummand M 0 := by
            ring
      _ = 0 + rfSummand M 0 := by rw [heq, sub_self]
      _ = rfSummand M 0 := zero_add _
  have hc : PowerSeries.constantCoeff (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) = 1 :=
    constantCoeff_one_add_X_pow (by omega)
  have hdiv : rfRem M - rfRem (M + 1) =
      rfSummand M 0 * inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) := by
    calc
      rfRem M - rfRem (M + 1)
          = (inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) *
              (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2))) * (rfRem M - rfRem (M + 1)) := by
            rw [inv1_mul hc, one_mul]
      _ = inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) *
            ((1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) * (rfRem M - rfRem (M + 1))) := by ring
      _ = rfSummand M 0 * inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) := by
            rw [hunit, mul_comm]
  rw [hdiv]
  unfold rfSummand
  simp only [pow_zero, one_mul, Nat.add_zero]
  have heven_mul : inv1 (rfEvenProd M) * inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) =
      inv1 (rfEvenProd (M + 1)) := by
    have hpr : rfEvenProd (M + 1) =
        rfEvenProd M * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2)) :=
      Finset.prod_range_succ _ M
    rw [hpr, inv1_mul_distrib (rfEvenProd_const M) hc]
  calc
    (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M 0 * inv1 (rfOddProd M) * inv1 (rfEvenProd M) *
        inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2))
        = (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M 0 * inv1 (rfOddProd M) *
            (inv1 (rfEvenProd M) * inv1 (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M + 2))) := by ring
    _ = (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M 0 * inv1 (rfOddProd M) * inv1 (rfEvenProd (M + 1)) := by
          rw [heven_mul]

private lemma rfRem_coeff_zero {d M : ℕ} (hdM : d < M) :
    PowerSeries.coeff d (rfRem M) = 0 := by
  rw [rfRem, PowerSeries.coeff_mk]
  refine Finset.sum_eq_zero fun r _ ↦ ?_
  unfold rfSummand
  have he : d < rfExp M r := by
    unfold rfExp
    omega
  have hrew : (-1 : ℤ⟦X⟧) ^ r * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M r *
      inv1 (rfOddProd (M + r)) * inv1 (rfEvenProd M) =
      (PowerSeries.X : ℤ⟦X⟧) ^ rfExp M r *
        ((-1 : ℤ⟦X⟧) ^ r * inv1 (rfOddProd (M + r)) * inv1 (rfEvenProd M)) := by ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero he _

private lemma one_add_X_mul_rfOddProd (m : ℕ) :
    (1 + (PowerSeries.X : ℤ⟦X⟧)) * rfOddProd m =
      ∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1)) := by
  induction m with
  | zero =>
    simp [rfOddProd]
  | succ m ih =>
    rw [rfOddProd, Finset.prod_range_succ, ← mul_assoc, ← rfOddProd, ih,
      finset_Icc_succ_right (by omega : 1 ≤ m + 1 + 1), Finset.prod_insert (by simp)]
    have hexp : 2 * (m + 1 + 1) - 1 = 2 * m + 3 := by omega
    rw [hexp, mul_comm]

private lemma odd_even_prod_eq_link1Prod (m : ℕ) :
    ((1 + (PowerSeries.X : ℤ⟦X⟧)) * rfOddProd m) * rfEvenProd (m + 1) =
      link1Prod 0 (2 * m + 2) := by
  induction m with
  | zero =>
    simp only [rfOddProd, rfEvenProd, link1Prod, Finset.prod_range_zero, Finset.prod_range_succ,
      mul_one, one_mul]
    ring
  | succ m ih =>
    have h1 : rfOddProd (m + 1) = rfOddProd m * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m + 3)) :=
      Finset.prod_range_succ _ m
    have h2 : rfEvenProd (m + 2) = rfEvenProd (m + 1) * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m + 4)) :=
      Finset.prod_range_succ _ (m + 1)
    have h3 : link1Prod 0 (2 * (m + 1) + 2) =
        link1Prod 0 (2 * m + 2) * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m + 3)) *
          (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m + 4)) := by
      unfold link1Prod
      have ha : 2 * (m + 1) + 2 = (2 * m + 2) + 1 + 1 := by omega
      rw [ha, Finset.prod_range_succ, Finset.prod_range_succ]
      have hb : 0 + 1 + (2 * m + 2) = 2 * m + 3 := by omega
      have hc : 0 + 1 + (2 * m + 2 + 1) = 2 * m + 4 := by omega
      rw [hb, hc]
    rw [h1, h2, h3, ← ih]
    ring

/-! ### Section 6: Link 4 — Shift-and-Cancel Induction for General `N ≥ 1` -/

private def c037OddProd (m : ℕ) : ℤ⟦X⟧ :=
  ∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))

private def c037EvenProd (N : ℕ) : ℤ⟦X⟧ :=
  ∏ j ∈ Finset.Icc 1 (N - 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j))

private lemma c037OddProd_const (m : ℕ) : PowerSeries.constantCoeff (c037OddProd m) = 1 := by
  refine constantCoeff_prod_one_add _ _ fun k hk ↦ ?_
  rw [Finset.mem_Icc] at hk
  omega

private lemma c037EvenProd_const (N : ℕ) : PowerSeries.constantCoeff (c037EvenProd N) = 1 := by
  refine constantCoeff_prod_one_add _ _ fun j hj ↦ ?_
  rw [Finset.mem_Icc] at hj
  omega

private def c037Summand (N m : ℕ) : ℤ⟦X⟧ :=
  (-1 : ℤ⟦X⟧) ^ (m + 1 + N) * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N * (m + 1) - N) *
    inv1 (c037OddProd m)

private lemma c037Summand_vanish {N : ℕ} (hN : 1 ≤ N) (d m : ℕ) (hm : d + 1 ≤ m) :
    PowerSeries.coeff d (c037Summand N m) = 0 := by
  unfold c037Summand
  have hexp : d < 2 * N * (m + 1) - N := by
    have hmul1 : 2 * m + 1 ≤ N * (2 * m + 1) := by
      simpa using Nat.mul_le_mul_right (2 * m + 1) hN
    have hmul2 : N * (2 * m + 1) + N = 2 * N * (m + 1) := by ring
    omega
  have hrew : (-1 : ℤ⟦X⟧) ^ (m + 1 + N) * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N * (m + 1) - N) *
      inv1 (c037OddProd m) =
      (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N * (m + 1) - N) *
        ((-1 : ℤ⟦X⟧) ^ (m + 1 + N) * inv1 (c037OddProd m)) := by ring
  rw [hrew]
  exact coeff_X_pow_mul_eq_zero hexp _

private def c037Tail (N : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun d ↦ ∑ m ∈ Finset.range (d + 1), PowerSeries.coeff d (c037Summand N m)

private lemma hasSum_c037Summand {N : ℕ} (hN : 1 ≤ N) :
    HasSum (c037Summand N) (c037Tail N) :=
  hasSum_mk_of_coeff_vanish (c037Summand N) (fun d ↦ d + 1) (c037Summand_vanish hN)

private lemma c037_shift_cancel {N : ℕ} (hN : 1 ≤ N) :
    (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N)) * c037Tail N =
      (-1 : ℤ⟦X⟧) ^ (N + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ N + c037Tail (N + 1) := by
  have hdiff_sum := (hasSum_c037Summand hN).sub (hasSum_c037Summand (by omega : 1 ≤ N + 1))
  have hterm0 : c037Summand N 0 - c037Summand (N + 1) 0 =
      (-1 : ℤ⟦X⟧) ^ (N + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ N := by
    unfold c037Summand c037OddProd
    have hIcc1 : Finset.Icc 1 1 = {1} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_singleton]
      omega
    have he1 : 2 * N * 1 - N = N := by omega
    have he2 : 2 * (N + 1) * 1 - (N + 1) = N + 1 := by omega
    rw [Nat.zero_add, hIcc1, Finset.prod_singleton, he1, he2]
    have hpow1 : (PowerSeries.X : ℤ⟦X⟧) ^ (2 * 1 - 1) = PowerSeries.X := by simp
    have hs1 : 1 + N = N + 1 := by omega
    have hs2 : 1 + (N + 1) = (N + 1) + 1 := by omega
    rw [hpow1, hs1, hs2, pow_add (-1 : ℤ⟦X⟧) (N + 1) 1,
      pow_add (PowerSeries.X : ℤ⟦X⟧) N 1, pow_one, pow_one]
    have hc1 : PowerSeries.constantCoeff (1 + (PowerSeries.X : ℤ⟦X⟧)) = 1 := by
      have := constantCoeff_one_add_X_pow (by omega : 0 < 1)
      rwa [pow_one] at this
    calc
      (-1 : ℤ⟦X⟧) ^ (N + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ N * inv1 (1 + PowerSeries.X) -
        (-1 : ℤ⟦X⟧) ^ (N + 1) * (-1) * ((PowerSeries.X : ℤ⟦X⟧) ^ N * PowerSeries.X) *
          inv1 (1 + PowerSeries.X)
          = (-1 : ℤ⟦X⟧) ^ (N + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ N *
              ((1 + PowerSeries.X) * inv1 (1 + PowerSeries.X)) := by ring
      _ = (-1 : ℤ⟦X⟧) ^ (N + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ N := by
            rw [mul_inv1 hc1, mul_one]
  have hterm_succ : ∀ r : ℕ,
      c037Summand N (r + 1) - c037Summand (N + 1) (r + 1) =
        -((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N) * c037Summand N r) := by
    intro r
    unfold c037Summand
    have hodd_split : c037OddProd (r + 1) =
        c037OddProd r * (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * r + 3)) := by
      unfold c037OddProd
      rw [finset_Icc_succ_right (by omega : 1 ≤ r + 1 + 1), Finset.prod_insert (by simp)]
      have : 2 * (r + 1 + 1) - 1 = 2 * r + 3 := by omega
      rw [this, mul_comm]
    have hcancel : (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * r + 3)) * inv1 (c037OddProd (r + 1)) =
        inv1 (c037OddProd r) := by
      rw [hodd_split]
      exact mul_inv1_cancel_right (c037OddProd_const r) (constantCoeff_one_add_X_pow (by omega))
    have he1 : 2 * N * (r + 1 + 1) - N = 2 * N + (2 * N * (r + 1) - N) := by
      have hsub : N ≤ 2 * N * (r + 1) := by
        have : 1 * 1 ≤ 2 * (r + 1) := by omega
        nlinarith
      have : 2 * N * (r + 1 + 1) = 2 * N + 2 * N * (r + 1) := by ring
      omega
    have he2 : 2 * (N + 1) * (r + 1 + 1) - (N + 1) =
        (2 * N + (2 * N * (r + 1) - N)) + (2 * r + 3) := by
      have hsub : N ≤ 2 * N * (r + 1) := by nlinarith
      have : 2 * (N + 1) * (r + 1 + 1) = 2 * N * (r + 1) + 2 * N + 2 * r + 4 := by ring
      omega
    have hs1 : r + 1 + 1 + N = (r + 1 + N) + 1 := by omega
    have hs2 : r + 1 + 1 + (N + 1) = (r + 1 + N) + 2 := by omega
    rw [he1, he2, hs1, hs2, pow_add (-1 : ℤ⟦X⟧) (r + 1 + N) 1,
      pow_add (-1 : ℤ⟦X⟧) (r + 1 + N) 2, pow_add (PowerSeries.X : ℤ⟦X⟧) _ (2 * r + 3),
      pow_add (PowerSeries.X : ℤ⟦X⟧) (2 * N) _]
    simp only [pow_one, pow_two]
    calc
      ((-1 : ℤ⟦X⟧) ^ (r + 1 + N) * (-1)) *
          ((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N) * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N * (r + 1) - N)) *
          inv1 (c037OddProd (r + 1)) -
        ((-1 : ℤ⟦X⟧) ^ (r + 1 + N) * ((-1) * (-1))) *
          ((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N) * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N * (r + 1) - N) *
            (PowerSeries.X : ℤ⟦X⟧) ^ (2 * r + 3)) *
          inv1 (c037OddProd (r + 1))
          = -((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N) * (-1 : ℤ⟦X⟧) ^ (r + 1 + N) *
              (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N * (r + 1) - N) *
              ((1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * r + 3)) * inv1 (c037OddProd (r + 1)))) := by
            ring
      _ = -((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N) *
            ((-1 : ℤ⟦X⟧) ^ (r + 1 + N) * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N * (r + 1) - N) *
              inv1 (c037OddProd r))) := by
            rw [hcancel]
            ring
  have hshift_rhs : HasSum (fun m ↦ c037Summand N m - c037Summand (N + 1) m)
      ((-1 : ℤ⟦X⟧) ^ (N + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ N -
        (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N) * c037Tail N) := by
    have h1 := ((hasSum_c037Summand hN).mul_left ((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N))).neg
    have h2 : HasSum (fun r ↦ c037Summand N (r + 1) - c037Summand (N + 1) (r + 1))
        (-((PowerSeries.X : ℤ⟦X⟧) ^ (2 * N) * c037Tail N)) :=
      h1.congr_fun fun r ↦ hterm_succ r
    have h3 := HasSum.zero_add (f := fun m ↦ c037Summand N m - c037Summand (N + 1) m) h2
    rwa [hterm0, ← sub_eq_add_neg] at h3
  have heq := hdiff_sum.unique hshift_rhs
  calc
    (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N)) * c037Tail N
        = (c037Tail N - c037Tail (N + 1)) + c037Tail (N + 1) +
            (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N) * c037Tail N := by ring
    _ = ((-1 : ℤ⟦X⟧) ^ (N + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ N -
          (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N) * c037Tail N) + c037Tail (N + 1) +
          (PowerSeries.X : ℤ⟦X⟧) ^ (2 * N) * c037Tail N := by rw [heq]
    _ = (-1 : ℤ⟦X⟧) ^ (N + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ N + c037Tail (N + 1) := by ring

/-! ### Pinned Target Theorems (`PIN-C037.md` v1) -/

/-- Fine's partition theorem (`OEIS A203568` `%F` lines 13–14, 19): connects `%N` (`a203568`) to
the generalized pentagonal numbers `pentagonal k = k * (3 * k - 1) / 2`. -/
theorem a203568_eq_pentagonal (n : ℕ) :
    a203568 n = if h : ∃ k : ℤ, pentagonal k = n then Int.sign h.choose else 0 := by
  have hcoeff := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (R := ℤ)).mp
    hasSum_pentagonal_a203568Series n
  rw [a203568Series, PowerSeries.coeff_mk] at hcoeff
  have hterm : ∀ k : ℕ,
      PowerSeries.coeff n
        ((PowerSeries.X : ℤ⟦X⟧) ^ pentagonal ((k : ℤ) + 1) -
          (PowerSeries.X : ℤ⟦X⟧) ^ pentagonal (-((k : ℤ) + 1))) =
      (if n = pentagonal ((k : ℤ) + 1) then (1 : ℤ) else 0) -
        (if n = pentagonal (-((k : ℤ) + 1)) then (1 : ℤ) else 0) := by
    intro k
    rw [map_sub, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
  simp_rw [hterm] at hcoeff
  split_ifs with hex
  · set z := hex.choose
    have hz : pentagonal z = n := hex.choose_spec
    rcases lt_trichotomy z 0 with hz_neg | hz0 | hz_pos
    · obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, z = -((k₀ : ℤ) + 1) := ⟨(-z - 1).toNat, by omega⟩
      have hsign : Int.sign z = -1 := by
        rw [hk₀]
        change Int.sign (Int.negSucc k₀) = -1
        rfl
      have hsingle : HasSum
          (fun k : ℕ ↦ (if n = pentagonal ((k : ℤ) + 1) then (1 : ℤ) else 0) -
            (if n = pentagonal (-((k : ℤ) + 1)) then (1 : ℤ) else 0)) (-1 : ℤ) := by
        have hs := hasSum_ite_eq k₀ (-1 : ℤ)
        refine hs.congr_fun fun k ↦ ?_
        have hne_pos : n ≠ pentagonal ((k : ℤ) + 1) := by
          intro hc
          have := pentagonal_injective (hz.trans hc)
          omega
        have hiff_neg : n = pentagonal (-((k : ℤ) + 1)) ↔ k = k₀ := by
          constructor
          · intro hc
            have := pentagonal_injective (hz.trans hc)
            omega
          · rintro rfl
            rw [← hz, hk₀]
        have hpos0 : (if n = pentagonal ((k : ℤ) + 1) then (1 : ℤ) else 0) = 0 := by
          by_cases ha : n = pentagonal ((k : ℤ) + 1)
          · exact (hne_pos ha).elim
          · simp only [ha, ↓reduceIte]
        rw [hpos0]
        by_cases hk : k = k₀
        · have hb : n = pentagonal (-((k : ℤ) + 1)) := hiff_neg.mpr hk
          simp only [hb, hk, ↓reduceIte]
          ring
        · have hb : ¬ (n = pentagonal (-((k : ℤ) + 1))) := mt hiff_neg.mp hk
          simp only [hb, hk, ↓reduceIte]
          ring
      rw [hsign]
      exact hcoeff.unique hsingle
    · have hn0 : n = 0 := by
        rw [hz0] at hz
        simpa [pentagonal] using hz.symm
      subst hn0
      have hzero_sum : HasSum
          (fun k : ℕ ↦ (if 0 = pentagonal ((k : ℤ) + 1) then (1 : ℤ) else 0) -
            (if 0 = pentagonal (-((k : ℤ) + 1)) then (1 : ℤ) else 0)) (0 : ℤ) := by
        convert hasSum_zero (α := ℤ) (β := ℕ) with k
        have h1 : ¬ (0 = pentagonal ((k : ℤ) + 1)) := by
          intro hc
          have hp0 : pentagonal (0 : ℤ) = 0 := rfl
          have := pentagonal_injective (hp0.trans hc)
          omega
        have h2 : ¬ (0 = pentagonal (-((k : ℤ) + 1))) := by
          intro hc
          have hp0 : pentagonal (0 : ℤ) = 0 := rfl
          have := pentagonal_injective (hp0.trans hc)
          omega
        simp only [h1, h2, ↓reduceIte, sub_self]
      rw [hz0]
      simpa using hcoeff.unique hzero_sum
    · obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, z = (k₀ : ℤ) + 1 := ⟨(z - 1).toNat, by omega⟩
      have hsign : Int.sign z = 1 := by
        rw [hk₀]
        change Int.sign (Int.ofNat (k₀ + 1)) = 1
        rfl
      have hsingle : HasSum
          (fun k : ℕ ↦ (if n = pentagonal ((k : ℤ) + 1) then (1 : ℤ) else 0) -
            (if n = pentagonal (-((k : ℤ) + 1)) then (1 : ℤ) else 0)) (1 : ℤ) := by
        have hs := hasSum_ite_eq k₀ (1 : ℤ)
        refine hs.congr_fun fun k ↦ ?_
        have hne_neg : ¬ (n = pentagonal (-((k : ℤ) + 1))) := by
          intro hc
          have := pentagonal_injective (hz.trans hc)
          omega
        have hiff_pos : n = pentagonal ((k : ℤ) + 1) ↔ k = k₀ := by
          constructor
          · intro hc
            have := pentagonal_injective (hz.trans hc)
            omega
          · rintro rfl
            rw [← hz, hk₀]
        simp only [hne_neg, ↓reduceIte, sub_zero]
        by_cases hk : k = k₀
        · have hb : n = pentagonal ((k : ℤ) + 1) := hiff_pos.mpr hk
          simp only [hb, hk, ↓reduceIte]
        · have hb : ¬ (n = pentagonal ((k : ℤ) + 1)) := mt hiff_pos.mp hk
          simp only [hb, hk, ↓reduceIte]
      rw [hsign]
      exact hcoeff.unique hsingle
  · have hzero_sum : HasSum
        (fun k : ℕ ↦ (if n = pentagonal ((k : ℤ) + 1) then (1 : ℤ) else 0) -
          (if n = pentagonal (-((k : ℤ) + 1)) then (1 : ℤ) else 0)) (0 : ℤ) := by
      convert hasSum_zero (α := ℤ) (β := ℕ) with k
      have h1 : ¬ (n = pentagonal ((k : ℤ) + 1)) := fun hc ↦ hex ⟨(k : ℤ) + 1, hc.symm⟩
      have h2 : ¬ (n = pentagonal (-((k : ℤ) + 1))) := fun hc ↦ hex ⟨-((k : ℤ) + 1), hc.symm⟩
      simp only [h1, h2, ↓reduceIte, sub_self]
    exact hcoeff.unique hzero_sum

/-- Closed-form sum-of-products formula for `c037Poly N` (`N ≥ 1`). -/
theorem c037Poly_closed_form (N : ℕ) (hN : 1 ≤ N) :
    c037Poly N = ∑ m ∈ Finset.Icc 1 (N - 1),
      (-1 : ℤ[X]) ^ (m + 1) * Polynomial.X ^ m *
        ∏ j ∈ Finset.Icc (m + 1) (N - 1), (1 + Polynomial.X ^ (2 * j)) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  clear hN
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero =>
    simp [c037Poly]
  | succ k ih =>
    rw [c037Poly_succ (by omega : 1 ≤ k + 1), ih, finset_Icc_succ_right (by omega : 1 ≤ k + 1),
      Finset.sum_insert (by simp)]
    have htop : ∏ j ∈ Finset.Icc (k + 1 + 1) (k + 1), (1 + (Polynomial.X : ℤ[X]) ^ (2 * j)) = 1 := by
      rw [finset_Icc_of_gt (by omega), Finset.prod_empty]
    have hrest :
        ∑ m ∈ Finset.Icc 1 k,
          (-1 : ℤ[X]) ^ (m + 1) * Polynomial.X ^ m *
            ∏ j ∈ Finset.Icc (m + 1) (k + 1), (1 + Polynomial.X ^ (2 * j)) =
        (1 + Polynomial.X ^ (2 * (k + 1))) *
          ∑ m ∈ Finset.Icc 1 k,
            (-1 : ℤ[X]) ^ (m + 1) * Polynomial.X ^ m *
              ∏ j ∈ Finset.Icc (m + 1) k, (1 + Polynomial.X ^ (2 * j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      rw [Finset.mem_Icc] at hm
      rw [finset_Icc_succ_right (by omega : m + 1 ≤ k + 1), Finset.prod_insert (by simp)]
      ring
    rw [htop, hrest]
    ring

/-- Pinned empirical polynomials `P(1, X)` through `P(4, X)` from `OEIS A203568` (`%F` line 26). -/
theorem c037Poly_empirical_values :
    c037Poly 1 = 0 ∧
      c037Poly 2 = Polynomial.X ∧
      c037Poly 3 = Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 5 ∧
      c037Poly 4 = Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 3 + Polynomial.X ^ 5 +
        Polynomial.X ^ 7 - Polynomial.X ^ 8 + Polynomial.X ^ 11 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [c037Poly]
    ring
  · change (1 + Polynomial.X ^ 4) * ((1 + Polynomial.X ^ 2) * 0 + (-1) ^ 2 * Polynomial.X ^ 1) +
        (-1) ^ 3 * Polynomial.X ^ 2 = _
    ring
  · change (1 + Polynomial.X ^ 6) *
        ((1 + Polynomial.X ^ 4) * ((1 + Polynomial.X ^ 2) * 0 + (-1) ^ 2 * Polynomial.X ^ 1) +
          (-1) ^ 3 * Polynomial.X ^ 2) +
        (-1) ^ 4 * Polynomial.X ^ 3 = _
    ring

/-- Exact degree `N^2 - N - 1` (in `WithBot ℕ`) and monicity of `c037Poly N` for all `1 < N`. -/
theorem c037Poly_degree_and_monic (N : ℕ) (hN : 1 < N) :
    (c037Poly N).degree = ((N ^ 2 - N - 1 : ℕ) : WithBot ℕ) ∧ (c037Poly N).Monic := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  clear hN
  induction k with
  | zero =>
    have h2 : c037Poly 2 = Polynomial.X := c037Poly_empirical_values.2.1
    rw [h2]
    exact ⟨Polynomial.degree_X, Polynomial.monic_X⟩
  | succ k ih =>
    set M := k + 2
    have hM2 : 2 ≤ M := by omega
    rw [show k + 1 + 2 = M + 1 by omega, c037Poly_succ (by omega : 1 ≤ M)]
    set fac : ℤ[X] := Polynomial.X ^ (2 * M) + Polynomial.C 1
    have hfac_eq : (1 + Polynomial.X ^ (2 * M) : ℤ[X]) = fac := by
      simp [fac, add_comm]
    have hfac_monic : fac.Monic := Polynomial.monic_X_pow_add_C 1 (by omega)
    have hfac_deg : fac.degree = ((2 * M : ℕ) : WithBot ℕ) := by
      change (Polynomial.X ^ (2 * M) + Polynomial.C (1 : ℤ)).degree = ((2 * M : ℕ) : WithBot ℕ)
      rw [Polynomial.degree_X_pow_add_C (by omega : 0 < 2 * M) (1 : ℤ)]
    rw [hfac_eq]
    have htop_monic : (fac * c037Poly M).Monic := hfac_monic.mul ih.2
    have htop_deg : (fac * c037Poly M).degree =
        (((M + 1) ^ 2 - (M + 1) - 1 : ℕ) : WithBot ℕ) := by
      rw [ih.2.degree_mul, hfac_deg, ih.1, ← Nat.cast_add, deg_step_arith hM2]
    have hlow_lt : ((-1 : ℤ[X]) ^ (M + 1) * Polynomial.X ^ M).degree <
        (fac * c037Poly M).degree := by
      rw [neg_one_pow_mul_X_pow_degree, htop_deg, Nat.cast_lt]
      exact lt_deg_step_arith hM2
    exact ⟨(Polynomial.degree_add_eq_left_of_degree_lt hlow_lt).trans htop_deg,
      htop_monic.add_of_left hlow_lt⟩

/-- `N = 1` reduction (`C036`, `OEIS A203568` `%F` line 24):
`A(X) = ∑_{n ≥ 1} (-1)^{n+1} X^{2n-1} / ∏_{k=1}^n (1 + X^{2k-1})` in `ℤ⟦X⟧`. -/
theorem c036_a203568_gf :
    HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 2) * PowerSeries.X ^ (2 * m + 1) *
      PowerSeries.invOfUnit
        (∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ))
      a203568Series := by
  have hrf_tel : HasSum (fun m : ℕ ↦
      (PowerSeries.X : ℤ⟦X⟧) ^ rfExp m 0 * inv1 (rfOddProd m) * inv1 (rfEvenProd (m + 1)))
      (rfRem 0) :=
    hasSum_of_sub_eq_and_coeff_zero rfRem _ rfRem_sub_succ (fun d M h ↦ rfRem_coeff_zero h)
  have hc1 : PowerSeries.constantCoeff (1 + (PowerSeries.X : ℤ⟦X⟧)) = 1 := by
    have := constantCoeff_one_add_X_pow (by omega : 0 < 1)
    rwa [pow_one] at this
  have hrhs := hrf_tel.mul_left ((PowerSeries.X : ℤ⟦X⟧) * inv1 (1 + PowerSeries.X))
  have hrhs_eq : HasSum (fun m : ℕ ↦
      (PowerSeries.X : ℤ⟦X⟧) ^ ((m + 1) * (2 * m + 1)) * inv1 (link1Prod 0 (2 * m + 2)))
      ((PowerSeries.X : ℤ⟦X⟧) * inv1 (1 + PowerSeries.X) * rfRem 0) := by
    refine hrhs.congr_fun fun m ↦ ?_
    have hexp : (PowerSeries.X : ℤ⟦X⟧) * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp m 0 =
        (PowerSeries.X : ℤ⟦X⟧) ^ ((m + 1) * (2 * m + 1)) := by
      rw [← one_add_rfExp_zero m, pow_add, pow_one]
    have hinv : inv1 (1 + PowerSeries.X) * inv1 (rfOddProd m) * inv1 (rfEvenProd (m + 1)) =
        inv1 (link1Prod 0 (2 * m + 2)) := by
      rw [← odd_even_prod_eq_link1Prod m,
        inv1_mul_distrib (by rw [map_mul, hc1, rfOddProd_const, mul_one]) (rfEvenProd_const _),
        inv1_mul_distrib hc1 (rfOddProd_const m)]
    exact (calc
      (PowerSeries.X : ℤ⟦X⟧) * inv1 (1 + PowerSeries.X) *
          ((PowerSeries.X : ℤ⟦X⟧) ^ rfExp m 0 * inv1 (rfOddProd m) * inv1 (rfEvenProd (m + 1)))
          = ((PowerSeries.X : ℤ⟦X⟧) * (PowerSeries.X : ℤ⟦X⟧) ^ rfExp m 0) *
              (inv1 (1 + PowerSeries.X) * inv1 (rfOddProd m) * inv1 (rfEvenProd (m + 1))) := by
            ring
      _ = (PowerSeries.X : ℤ⟦X⟧) ^ ((m + 1) * (2 * m + 1)) * inv1 (link1Prod 0 (2 * m + 2)) := by
            rw [hexp, hinv]).symm
  have hval : (PowerSeries.X : ℤ⟦X⟧) * inv1 (1 + PowerSeries.X) * rfRem 0 = a203568Series :=
    hrhs_eq.unique hasSum_entry944_a203568Series
  have hlhs := (hasSum_rfSummand 0).mul_left ((PowerSeries.X : ℤ⟦X⟧) * inv1 (1 + PowerSeries.X))
  rw [hval] at hlhs
  refine hlhs.congr_fun fun m ↦ ?_
  unfold rfSummand
  have hexp0 : rfExp 0 m = 2 * m := by
    unfold rfExp
    ring
  rw [hexp0, Nat.zero_add, rfEvenProd, Finset.prod_range_zero, inv1_one, mul_one]
  have hinv_odd : inv1 (1 + PowerSeries.X) * inv1 (rfOddProd m) =
      inv1 (∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) := by
    rw [← one_add_X_mul_rfOddProd m, inv1_mul_distrib hc1 (rfOddProd_const m)]
  have hsign : (-1 : ℤ⟦X⟧) ^ m = (-1 : ℤ⟦X⟧) ^ (m + 2) := by
    rw [pow_add, show (-1 : ℤ⟦X⟧) ^ 2 = 1 by ring, mul_one]
  have hpow : (PowerSeries.X : ℤ⟦X⟧) * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m) =
      (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m + 1) := by
    rw [pow_add, pow_one, mul_comm]
  exact (calc
    (PowerSeries.X : ℤ⟦X⟧) * inv1 (1 + PowerSeries.X) *
        ((-1 : ℤ⟦X⟧) ^ m * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m) * inv1 (rfOddProd m))
        = (-1 : ℤ⟦X⟧) ^ m * ((PowerSeries.X : ℤ⟦X⟧) * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m)) *
            (inv1 (1 + PowerSeries.X) * inv1 (rfOddProd m)) := by ring
    _ = (-1 : ℤ⟦X⟧) ^ (m + 2) * (PowerSeries.X : ℤ⟦X⟧) ^ (2 * m + 1) *
          inv1 (∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) := by
          rw [hsign, hpow, hinv_odd]).symm

private lemma evenProd_mul_a203568Series (N : ℕ) (hN : 1 ≤ N) :
    c037EvenProd N * a203568Series =
      Polynomial.toPowerSeries (c037Poly N) + c037Tail N := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  clear hN
  induction k with
  | zero =>
    have heven1 : c037EvenProd 1 = 1 := by
      simp [c037EvenProd]
    have htail1 : c037Tail 1 = a203568Series := by
      have h1 := hasSum_c037Summand (le_refl 1)
      have hc036 := c036_a203568_gf
      have hfun : c037Summand 1 = fun m : ℕ ↦
          (-1 : ℤ⟦X⟧) ^ (m + 2) * PowerSeries.X ^ (2 * m + 1) *
            inv1 (∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) := by
        funext m
        unfold c037Summand c037OddProd
        have hs : m + 1 + 1 = m + 2 := by omega
        have he : 2 * 1 * (m + 1) - 1 = 2 * m + 1 := by omega
        rw [hs, he]
      rw [hfun] at h1
      exact h1.unique hc036
    rw [heven1, one_mul, htail1]
    simp [c037Poly]
  | succ k ih =>
    set M := k + 1
    have hM : 1 ≤ M := by omega
    have heven_step : c037EvenProd (M + 1) =
        (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M)) * c037EvenProd M := by
      change (∏ j ∈ Finset.Icc 1 (k + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j))) =
        (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * (k + 1))) *
          ∏ j ∈ Finset.Icc 1 k, (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j))
      rw [finset_Icc_succ_right (by omega : 1 ≤ k + 1), Finset.prod_insert (by simp)]
    have hpoly_step : Polynomial.toPowerSeries (c037Poly (M + 1)) =
        (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M)) * Polynomial.toPowerSeries (c037Poly M) +
          (-1 : ℤ⟦X⟧) ^ (M + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ M := by
      rw [c037Poly_succ hM]
      change ((c037Poly (M + 1) : ℤ[X]) : ℤ⟦X⟧) = _
      rw [c037Poly_succ hM]
      push_cast
      rfl
    have hshift := c037_shift_cancel hM
    calc
      c037EvenProd (M + 1) * a203568Series
          = (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M)) * (c037EvenProd M * a203568Series) := by
            rw [heven_step, mul_assoc]
      _ = (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M)) * Polynomial.toPowerSeries (c037Poly M) +
            (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M)) * c037Tail M := by
            rw [ih, mul_add]
      _ = (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * M)) * Polynomial.toPowerSeries (c037Poly M) +
            ((-1 : ℤ⟦X⟧) ^ (M + 1) * (PowerSeries.X : ℤ⟦X⟧) ^ M + c037Tail (M + 1)) := by
            rw [hshift]
      _ = Polynomial.toPowerSeries (c037Poly (M + 1)) + c037Tail (M + 1) := by
            rw [hpoly_step]
            ring

/-- Explicit `N ≥ 1` Rogers–Fine family identity (`C037`) with `P(N, X) = c037Poly N`. -/
theorem c037_a203568_family_explicit (N : ℕ) (hN : 1 ≤ N) :
    ∃ S : ℤ⟦X⟧,
      HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1 + N) * PowerSeries.X ^ (2 * N * (m + 1) - N) *
        PowerSeries.invOfUnit
          (∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
      a203568Series =
        PowerSeries.invOfUnit
          (∏ j ∈ Finset.Icc 1 (N - 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j))) (1 : ℤˣ) *
          (Polynomial.toPowerSeries (c037Poly N) + S) := by
  refine ⟨c037Tail N, hasSum_c037Summand hN, ?_⟩
  have hmul := evenProd_mul_a203568Series N hN
  calc
    a203568Series
        = (inv1 (c037EvenProd N) * c037EvenProd N) * a203568Series := by
          rw [inv1_mul (c037EvenProd_const N), one_mul]
    _ = inv1 (c037EvenProd N) * (c037EvenProd N * a203568Series) := by ring
    _ = inv1 (c037EvenProd N) * (Polynomial.toPowerSeries (c037Poly N) + c037Tail N) := by
          rw [hmul]

/-- Unique existential form (`∃! P : ℤ[X], ...`) of Peter Bala's `C037` conjecture (`N ≥ 1`). -/
theorem c037_a203568_family (N : ℕ) (hN : 1 ≤ N) :
    ∃! P : ℤ[X],
      ((N = 1 → P = 0) ∧ (1 < N → P.degree = ((N ^ 2 - N - 1 : ℕ) : WithBot ℕ))) ∧
      ∃ S : ℤ⟦X⟧,
        HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1 + N) * PowerSeries.X ^ (2 * N * (m + 1) - N) *
          PowerSeries.invOfUnit
            (∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
        a203568Series =
          PowerSeries.invOfUnit
            (∏ j ∈ Finset.Icc 1 (N - 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j))) (1 : ℤˣ) *
            (Polynomial.toPowerSeries P + S) := by
  refine ⟨c037Poly N, ⟨⟨?_, ?_⟩, c037_a203568_family_explicit N hN⟩, ?_⟩
  · rintro rfl
    rfl
  · intro hlt
    exact (c037Poly_degree_and_monic N hlt).1
  · rintro Q ⟨_, S', hS'_sum, hQ_eq⟩
    have hS'_eq : S' = c037Tail N := hS'_sum.unique (hasSum_c037Summand hN)
    rw [hS'_eq] at hQ_eq
    have hlhs : c037EvenProd N * a203568Series =
        Polynomial.toPowerSeries Q + c037Tail N := by
      calc
        c037EvenProd N * a203568Series
            = c037EvenProd N * (inv1 (c037EvenProd N) *
                (Polynomial.toPowerSeries Q + c037Tail N)) := by rw [hQ_eq]; rfl
        _ = (c037EvenProd N * inv1 (c037EvenProd N)) *
              (Polynomial.toPowerSeries Q + c037Tail N) := by ring
        _ = Polynomial.toPowerSeries Q + c037Tail N := by
              rw [mul_inv1 (c037EvenProd_const N), one_mul]
    have hrhs := evenProd_mul_a203568Series N hN
    have hpoly_ps : Polynomial.toPowerSeries Q = Polynomial.toPowerSeries (c037Poly N) := by
      have hboth : Polynomial.toPowerSeries Q + c037Tail N =
          Polynomial.toPowerSeries (c037Poly N) + c037Tail N := hlhs.symm.trans hrhs
      exact add_right_cancel hboth
    exact Polynomial.coe_inj.mp hpoly_ps

/-- Verbatim existential corollary (`∃ P : ℤ[X], ...`) of Peter Bala's `C037` conjecture (`N ≥ 1`). -/
theorem c037_a203568_family_exists (N : ℕ) (hN : 1 ≤ N) :
    ∃ P : ℤ[X],
      ((N = 1 → P = 0) ∧ (1 < N → P.degree = ((N ^ 2 - N - 1 : ℕ) : WithBot ℕ))) ∧
      ∃ S : ℤ⟦X⟧,
        HasSum (fun m : ℕ ↦ (-1 : ℤ⟦X⟧) ^ (m + 1 + N) * PowerSeries.X ^ (2 * N * (m + 1) - N) *
          PowerSeries.invOfUnit
            (∏ k ∈ Finset.Icc 1 (m + 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * k - 1))) (1 : ℤˣ)) S ∧
        a203568Series =
          PowerSeries.invOfUnit
            (∏ j ∈ Finset.Icc 1 (N - 1), (1 + (PowerSeries.X : ℤ⟦X⟧) ^ (2 * j))) (1 : ℤˣ) *
            (Polynomial.toPowerSeries P + S) := by
  exact (c037_a203568_family N hN).exists

end

/-! ### Section 7: Decoupled Computable Mirror, OEIS Spot Checks, and Boundary Calibration -/

/-- Constructive subset-sum recurrence counting subsets of `{1, ..., k}` summing to `m`. -/
def subsetSumCount : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, m => subsetSumCount k m + if k + 1 ≤ m then subsetSumCount k (m - (k + 1)) else 0

/-- Linear-time `O(B)` shifted list addition `xs[n] + (if shift ≤ n then ys[n - shift] else 0)`. -/
def shiftAdd (shift : ℕ) (xs ys : List ℕ) : List ℕ :=
  List.zipWith (· + ·) xs (List.replicate shift 0 ++ ys)

/-- Single-pass `O(B^2)` constructive DP returning `(subsetSumRow_K, oddMaxCounts, evenMaxCounts)` up to `B`. -/
def distinctMaxParityDP (B : ℕ) : ℕ → List ℕ × List ℕ × List ℕ
  | 0 => (1 :: List.replicate B 0, List.replicate (B + 1) 0, List.replicate (B + 1) 0)
  | k + 1 =>
      let st := distinctMaxParityDP B k
      let row := st.1
      let oddAcc := st.2.1
      let evenAcc := st.2.2
      let oddAcc' := if (k + 1) % 2 = 1 then shiftAdd (k + 1) oddAcc row else oddAcc
      let evenAcc' := if (k + 1) % 2 = 0 then shiftAdd (k + 1) evenAcc row else evenAcc
      (shiftAdd (k + 1) row row, oddAcc', evenAcc')

/-- Constructive table `[A026837(0), ..., A026837(B)]`. -/
def a026837Table (B : ℕ) : List ℕ :=
  (distinctMaxParityDP B B).2.1

/-- Constructive table `[A026838(0), ..., A026838(B)]`. -/
def a026838Table (B : ℕ) : List ℕ :=
  (distinctMaxParityDP B B).2.2

/-- Constructive table `[A203568(0), ..., A203568(B)]`. -/
def a203568Table (B : ℕ) : List ℤ :=
  List.zipWith (fun (a b : ℕ) ↦ (a : ℤ) - (b : ℤ)) (a026837Table B) (a026838Table B)

/-- Pointwise constructive mirror for `a026837`. -/
def a026837Compute (n : ℕ) : ℕ :=
  (a026837Table n).getD n 0

/-- Pointwise constructive mirror for `a026838`. -/
def a026838Compute (n : ℕ) : ℕ :=
  (a026838Table n).getD n 0

/-- Pointwise constructive mirror for `a203568`. -/
def a203568Compute (n : ℕ) : ℤ :=
  (a026837Compute n : ℤ) - (a026838Compute n : ℤ)

private lemma subsetSumFinset_card (k m : ℕ) :
    (subsetSumFinset k m).card = subsetSumCount k m := by
  induction k generalizing m with
  | zero =>
    have hIcc : Finset.Icc 1 0 = ∅ := finset_Icc_of_gt (by omega)
    cases m with
    | zero =>
      have hset : subsetSumFinset 0 0 = {∅} := by
        ext s
        simp only [subsetSumFinset, hIcc, Finset.powerset_empty, Finset.mem_filter,
          Finset.mem_singleton]
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, by simp [h]⟩⟩
      rw [hset]
      rfl
    | succ r =>
      have hset : subsetSumFinset 0 (r + 1) = ∅ := by
        ext s
        simp only [subsetSumFinset, hIcc, Finset.powerset_empty, Finset.mem_filter,
          Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨rfl, hsum⟩
        simp at hsum
      rw [hset]
      rfl
  | succ k ih =>
    rw [subsetSumCount]
    have hsplit := (Finset.card_filter_add_card_filter_not
      (s := subsetSumFinset (k + 1) m) (p := fun s : Finset ℕ ↦ k + 1 ∈ s)).symm
    rw [hsplit, add_comm]
    congr 1
    · have hnot : (subsetSumFinset (k + 1) m).filter (fun s ↦ k + 1 ∉ s) =
          subsetSumFinset k m := by
        ext s
        simp only [subsetSumFinset, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · rintro ⟨⟨hsub, hsum⟩, hnot⟩
          refine ⟨fun x hx ↦ ?_, hsum⟩
          have hxI := Finset.mem_Icc.mp (hsub hx)
          have hne : x ≠ k + 1 := fun hc ↦ hnot (hc ▸ hx)
          rw [Finset.mem_Icc]
          omega
        · rintro ⟨hsub, hsum⟩
          refine ⟨⟨fun x hx ↦ ?_, hsum⟩, fun hc ↦ ?_⟩
          · have hxI := Finset.mem_Icc.mp (hsub hx)
            rw [Finset.mem_Icc]
            omega
          · have := Finset.mem_Icc.mp (hsub hc)
            omega
      rw [hnot, ih m]
    · split_ifs with hkm
      · rw [← ih (m - (k + 1))]
        refine Finset.card_bij
          (fun (s : Finset ℕ) (_ : s ∈ (subsetSumFinset (k + 1) m).filter (fun s ↦ k + 1 ∈ s)) ↦
            s.erase (k + 1))
          ?_ ?_ ?_
        · intro s hs
          simp only [subsetSumFinset, Finset.mem_filter, Finset.mem_powerset] at hs ⊢
          rcases hs with ⟨⟨hsub, hsum⟩, hmem⟩
          refine ⟨fun x hx ↦ ?_, ?_⟩
          · rw [Finset.mem_erase] at hx
            have hxI := Finset.mem_Icc.mp (hsub hx.2)
            rw [Finset.mem_Icc]
            omega
          · have hadd := Finset.add_sum_erase s (fun j ↦ j) hmem
            omega
        · intro s₁ hs₁ s₂ hs₂ heq
          have hm₁ : k + 1 ∈ s₁ := (Finset.mem_filter.mp hs₁).2
          have hm₂ : k + 1 ∈ s₂ := (Finset.mem_filter.mp hs₂).2
          rw [← Finset.insert_erase hm₁, ← Finset.insert_erase hm₂, heq]
        · intro t ht
          simp only [subsetSumFinset, Finset.mem_filter, Finset.mem_powerset] at ht
          rcases ht with ⟨hsub, hsum⟩
          have hnot : k + 1 ∉ t := fun hc ↦ by
            have := Finset.mem_Icc.mp (hsub hc)
            omega
          refine ⟨insert (k + 1) t, ?_, Finset.erase_insert hnot⟩
          simp only [subsetSumFinset, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨⟨fun x hx ↦ ?_, ?_⟩, Finset.mem_insert_self (k + 1) t⟩
          · rw [Finset.mem_insert] at hx
            rcases hx with rfl | hxt
            · rw [Finset.mem_Icc]; omega
            · have := Finset.mem_Icc.mp (hsub hxt)
              rw [Finset.mem_Icc]; omega
          · rw [Finset.sum_insert hnot, hsum]
            omega
      · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro s hs
        simp only [subsetSumFinset, Finset.mem_filter] at hs
        have hadd := Finset.add_sum_erase s (fun j ↦ j) hs.2
        omega

private lemma shiftAdd_length (shift : ℕ) (xs ys : List ℕ) (h : xs.length ≤ shift + ys.length) :
    (shiftAdd shift xs ys).length = xs.length := by
  rw [shiftAdd, List.length_zipWith, List.length_append, List.length_replicate]
  omega

private lemma replicate_zero_append_getD (shift : ℕ) (ys : List ℕ) (m : ℕ) :
    (List.replicate shift 0 ++ ys).getD m 0 =
      if shift ≤ m then ys.getD (m - shift) 0 else 0 := by
  induction shift generalizing m with
  | zero => simp
  | succ s ih =>
    cases m with
    | zero => simp [List.replicate_succ]
    | succ r =>
      simp only [List.replicate_succ, List.cons_append, List.getD_cons_succ,
        Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub]
      exact ih r

private lemma zipWith_add_getD (xs zs : List ℕ) {m : ℕ}
    (hx : m < xs.length) (hz : m < zs.length) :
    (List.zipWith (· + ·) xs zs).getD m 0 = xs.getD m 0 + zs.getD m 0 := by
  induction xs generalizing zs m with
  | nil => cases hx
  | cons a xs ih =>
    cases zs with
    | nil => cases hz
    | cons b zs =>
      cases m with
      | zero => rfl
      | succ r =>
        simp only [List.getD_cons_succ]
        exact ih zs (Nat.lt_of_succ_lt_succ hx) (Nat.lt_of_succ_lt_succ hz)

private lemma shiftAdd_getD (shift : ℕ) (xs ys : List ℕ) {m : ℕ}
    (hx : m < xs.length) (hy : m < shift + ys.length) :
    (shiftAdd shift xs ys).getD m 0 =
      xs.getD m 0 + if shift ≤ m then ys.getD (m - shift) 0 else 0 := by
  have hz : m < (List.replicate shift 0 ++ ys).length := by
    rw [List.length_append, List.length_replicate]
    exact hy
  rw [shiftAdd, zipWith_add_getD xs _ hx hz, replicate_zero_append_getD]

private lemma distinctMaxParityDP_row_length (B K : ℕ) :
    (distinctMaxParityDP B K).1.length = B + 1 := by
  induction K with
  | zero => simp [distinctMaxParityDP]
  | succ k ih =>
    change (shiftAdd (k + 1) (distinctMaxParityDP B k).1 (distinctMaxParityDP B k).1).length = B + 1
    rw [shiftAdd_length _ _ _ (by omega), ih]

private lemma distinctMaxParityDP_spec (B K : ℕ) :
    (∀ m ≤ B, (distinctMaxParityDP B K).1.getD m 0 = subsetSumCount K m) ∧
    (distinctMaxParityDP B K).2.1.length = B + 1 ∧
    (distinctMaxParityDP B K).2.2.length = B + 1 ∧
    (∀ n ≤ B, (distinctMaxParityDP B K).2.1.getD n 0 =
      ∑ k ∈ (Finset.range K).filter (fun k ↦ Odd (k + 1)),
        if k + 1 ≤ n then subsetSumCount k (n - (k + 1)) else 0) ∧
    (∀ n ≤ B, (distinctMaxParityDP B K).2.2.getD n 0 =
      ∑ k ∈ (Finset.range K).filter (fun k ↦ Even (k + 1)),
        if k + 1 ≤ n then subsetSumCount k (n - (k + 1)) else 0) := by
  induction K with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro m hm
      cases m with
      | zero => rfl
      | succ r =>
        simp only [distinctMaxParityDP, subsetSumCount, List.getD_cons_succ]
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        have hr : r < B := by omega
        simp [hr]
    · simp [distinctMaxParityDP]
    · simp [distinctMaxParityDP]
    · intro n hn
      simp only [distinctMaxParityDP, List.getD_eq_getElem?_getD, List.getElem?_replicate,
        Finset.range_zero, Finset.filter_empty, Finset.sum_empty]
      have hn' : n < B + 1 := by omega
      simp [hn']
    · intro n hn
      simp only [distinctMaxParityDP, List.getD_eq_getElem?_getD, List.getElem?_replicate,
        Finset.range_zero, Finset.filter_empty, Finset.sum_empty]
      have hn' : n < B + 1 := by omega
      simp [hn']
  | succ k ih =>
    rcases ih with ⟨hrow, hlen_odd, hlen_even, hodd, heven⟩
    have hlen_row : (distinctMaxParityDP B k).1.length = B + 1 := distinctMaxParityDP_row_length B k
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro m hm
      change (shiftAdd (k + 1) (distinctMaxParityDP B k).1 (distinctMaxParityDP B k).1).getD m 0 =
        subsetSumCount (k + 1) m
      rw [shiftAdd_getD (k + 1) _ _ (by omega) (by omega), subsetSumCount, hrow m hm]
      split_ifs with hkm
      · rw [hrow (m - (k + 1)) (by omega)]
      · rfl
    · simp only [distinctMaxParityDP]
      split_ifs
      · rw [shiftAdd_length _ _ _ (by omega), hlen_odd]
      · exact hlen_odd
    · simp only [distinctMaxParityDP]
      split_ifs
      · rw [shiftAdd_length _ _ _ (by omega), hlen_even]
      · exact hlen_even
    · intro n hn
      simp only [distinctMaxParityDP]
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hk_odd : Odd (k + 1)
      · have hmod : (k + 1) % 2 = 1 := Nat.odd_iff.mp hk_odd
        simp only [hmod, hk_odd, ↓reduceIte,
          Finset.sum_insert (by simp : k ∉ (Finset.range k).filter _)]
        rw [shiftAdd_getD (k + 1) _ _ (by omega) (by omega), hodd n hn, add_comm]
        congr 1
        split_ifs with hkn
        · exact hrow (n - (k + 1)) (by omega)
        · rfl
      · have hmod : (k + 1) % 2 ≠ 1 := fun hc ↦ hk_odd (Nat.odd_iff.mpr hc)
        simp only [hmod, hk_odd, ↓reduceIte]
        exact hodd n hn
    · intro n hn
      simp only [distinctMaxParityDP]
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hk_even : Even (k + 1)
      · have hmod : (k + 1) % 2 = 0 := Nat.even_iff.mp hk_even
        simp only [hmod, hk_even, ↓reduceIte,
          Finset.sum_insert (by simp : k ∉ (Finset.range k).filter _)]
        rw [shiftAdd_getD (k + 1) _ _ (by omega) (by omega), heven n hn, add_comm]
        congr 1
        split_ifs with hkn
        · exact hrow (n - (k + 1)) (by omega)
        · rfl
      · have hmod : (k + 1) % 2 ≠ 0 := fun hc ↦ hk_even (Nat.even_iff.mpr hc)
        simp only [hmod, hk_even, ↓reduceIte]
        exact heven n hn

theorem a026837Table_getD_eq {B n : ℕ} (hn : n ≤ B) :
    (a026837Table B).getD n 0 = a026837 n := by
  rw [a026837Table, (distinctMaxParityDP_spec B B).2.2.2.1 n hn, a026837,
    card_distincts_maxPart_prop n Odd]
  have hsub : (Finset.range n).filter (fun k ↦ Odd (k + 1)) ⊆
      (Finset.range B).filter (fun k ↦ Odd (k + 1)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨by omega, hk.2⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr (by ext k; simp) fun k _ ↦ ?_
    rw [maxPartDistincts_card_eq_subsetSum]
    split_ifs with hkn
    · exact (subsetSumFinset_card k (n - (k + 1))).symm
    · rfl
  · intro k hkB hkn
    simp only [Finset.mem_filter, Finset.mem_range] at hkB
    have hk_ge : ¬ (k < n) := fun hlt ↦ hkn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hkB.2⟩)
    have : ¬ (k + 1 ≤ n) := by omega
    simp [this]

theorem a026838Table_getD_eq {B n : ℕ} (hn : n ≤ B) :
    (a026838Table B).getD n 0 = a026838 n := by
  rw [a026838Table, (distinctMaxParityDP_spec B B).2.2.2.2 n hn, a026838,
    card_distincts_maxPart_prop n Even]
  have hsub : (Finset.range n).filter (fun k ↦ Even (k + 1)) ⊆
      (Finset.range B).filter (fun k ↦ Even (k + 1)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨by omega, hk.2⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr (by ext k; simp) fun k _ ↦ ?_
    rw [maxPartDistincts_card_eq_subsetSum]
    split_ifs with hkn
    · exact (subsetSumFinset_card k (n - (k + 1))).symm
    · rfl
  · intro k hkB hkn
    simp only [Finset.mem_filter, Finset.mem_range] at hkB
    have hk_ge : ¬ (k < n) := fun hlt ↦ hkn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hkB.2⟩)
    have : ¬ (k + 1 ≤ n) := by omega
    simp [this]

/-- Decoupled constructive equivalence `a026837 = a026837Compute` (proved directly from
`Nat.Partition.distincts`, without routing through `a203568_eq_pentagonal`). -/
theorem a026837_eq_compute (n : ℕ) : a026837 n = a026837Compute n :=
  (a026837Table_getD_eq (le_refl n)).symm

/-- Decoupled constructive equivalence `a026838 = a026838Compute`. -/
theorem a026838_eq_compute (n : ℕ) : a026838 n = a026838Compute n :=
  (a026838Table_getD_eq (le_refl n)).symm

/-- Decoupled constructive equivalence `a203568 = a203568Compute`. -/
theorem a203568_eq_compute (n : ℕ) : a203568 n = a203568Compute n := by
  rw [a203568, a203568Compute, a026837_eq_compute, a026838_eq_compute]

private lemma map_range_a026837_succ (B : ℕ) :
    (List.range B).map (fun i ↦ a026837 (i + 1)) = (a026837Table B).tail := by
  have hlen : (a026837Table B).length = B + 1 := (distinctMaxParityDP_spec B B).2.1
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi₁ hi₂
    rw [List.getElem_map, List.getElem_range, List.getElem_tail]
    have hle : i + 1 ≤ B := by simp at hi₁; omega
    rw [← a026837Table_getD_eq hle, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl

private lemma map_range_a026838_succ (B : ℕ) :
    (List.range B).map (fun i ↦ a026838 (i + 1)) = (a026838Table B).tail := by
  have hlen : (a026838Table B).length = B + 1 := (distinctMaxParityDP_spec B B).2.2.1
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi₁ hi₂
    rw [List.getElem_map, List.getElem_range, List.getElem_tail]
    have hle : i + 1 ≤ B := by simp at hi₁; omega
    rw [← a026838Table_getD_eq hle, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl

private lemma zipWith_sub_getD (xs ys : List ℕ) {n : ℕ}
    (hx : n < xs.length) (hy : n < ys.length) :
    (List.zipWith (fun (a b : ℕ) ↦ (a : ℤ) - (b : ℤ)) xs ys).getD n 0 =
      (xs.getD n 0 : ℤ) - (ys.getD n 0 : ℤ) := by
  induction xs generalizing ys n with
  | nil => cases hx
  | cons a xs ih =>
    cases ys with
    | nil => cases hy
    | cons b ys =>
      cases n with
      | zero => rfl
      | succ r =>
        simp only [List.getD_cons_succ]
        exact ih ys (Nat.lt_of_succ_lt_succ hx) (Nat.lt_of_succ_lt_succ hy)

private lemma map_range_a203568 (B : ℕ) :
    (List.range (B + 1)).map a203568 = a203568Table B := by
  have hlen1 : (a026837Table B).length = B + 1 := (distinctMaxParityDP_spec B B).2.1
  have hlen2 : (a026838Table B).length = B + 1 := (distinctMaxParityDP_spec B B).2.2.1
  have hlenZ : (a203568Table B).length = B + 1 := by
    rw [a203568Table, List.length_zipWith, hlen1, hlen2]
    omega
  apply List.ext_getElem
  · simp [hlenZ]
  · intro n hn₁ hn₂
    rw [List.getElem_map, List.getElem_range]
    have hle : n ≤ B := by simp at hn₁; omega
    have hrhs : (a203568Table B)[n] = (a203568Table B).getD n 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn₂]
      rfl
    rw [hrhs, a203568Table, zipWith_sub_getD _ _ (by omega) (by omega),
      a203568, a026837Table_getD_eq hle, a026838Table_getD_eq hle]

/-- Kernel-verified agreement of `a026837` on all 54 printed terms (`n = 1..54`) of `OEIS A026837`
(`%S/%T/%U`, offset `1`). -/
theorem a026837_oeis_54 :
    (List.range 54).map (fun i ↦ a026837 (i + 1)) =
      [1, 0, 1, 1, 2, 2, 2, 3, 4, 5, 6, 8, 9, 11, 13, 16, 19, 23, 27, 32, 38, 45, 52, 61,
       71, 82, 96, 111, 128, 148, 170, 195, 224, 256, 293, 334, 380, 432, 491, 556, 630,
       713, 805, 908, 1024, 1152, 1295, 1455, 1632, 1829, 2049, 2291, 2560, 2859] := by
  rw [map_range_a026837_succ]
  rfl

/-- Kernel-verified agreement of `a026838` on all 54 printed terms (`n = 1..54`) of `OEIS A026838`
(`%S/%T/%U`, offset `1`). -/
theorem a026838_oeis_54 :
    (List.range 54).map (fun i ↦ a026838 (i + 1)) =
      [0, 1, 1, 1, 1, 2, 3, 3, 4, 5, 6, 7, 9, 11, 14, 16, 19, 23, 27, 32, 38, 44, 52, 61,
       71, 83, 96, 111, 128, 148, 170, 195, 224, 256, 292, 334, 380, 432, 491, 557, 630,
       713, 805, 908, 1024, 1152, 1295, 1455, 1632, 1829, 2048, 2291, 2560, 2859] := by
  rw [map_range_a026838_succ]
  rfl

/-- Kernel-verified agreement of `a203568` on all 105 printed terms (`n = 0..104`) of
`OEIS A203568` (`%S/%T/%U`, offset `0`). -/
theorem a203568_oeis_105 :
    (List.range 105).map a203568 =
      [0, 1, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1,
       0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
       0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] := by
  rw [show (105 : ℕ) = 104 + 1 from rfl, map_range_a203568]
  rfl

/-- `P(5, X)` explicit polynomial and verification of its `+2 X^11` coefficient (the first `N`
with a coefficient outside `{-1, 0, +1}`, arising from `X^8 * X^3 + 1 * X^11`). -/
theorem c037Poly_five_and_coeff_11 :
    c037Poly 5 =
      Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 3 - Polynomial.X ^ 4 +
        Polynomial.X ^ 5 + Polynomial.X ^ 7 - Polynomial.X ^ 8 + Polynomial.X ^ 9 -
        Polynomial.X ^ 10 + 2 * Polynomial.X ^ 11 + Polynomial.X ^ 13 +
        Polynomial.X ^ 15 - Polynomial.X ^ 16 + Polynomial.X ^ 19 ∧
      (c037Poly 5).coeff 11 = 2 := by
  have h5 : c037Poly 5 =
      Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 3 - Polynomial.X ^ 4 +
        Polynomial.X ^ 5 + Polynomial.X ^ 7 - Polynomial.X ^ 8 + Polynomial.X ^ 9 -
        Polynomial.X ^ 10 + 2 * Polynomial.X ^ 11 + Polynomial.X ^ 13 +
        Polynomial.X ^ 15 - Polynomial.X ^ 16 + Polynomial.X ^ 19 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, c037Poly_succ (by omega),
      c037Poly_empirical_values.2.2.2]
    ring
  refine ⟨h5, ?_⟩
  rw [h5]
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X]

/-- Boundary calibration at `N = 1` (degree `⊥`, empty even product `1`, reduction to `C036`) and
`N = 2` (`P(2, X) = X`, low-degree coefficientwise agreement `[0, 1, -1, 1, -1, 1, 0]` for
`X + S_2(X) = (1 + X^2) A(X)` across degrees `0..6`). -/
theorem c037_boundary_calibration :
    (c037Poly 1).degree = ⊥ ∧
    c037Poly 2 = Polynomial.X ∧
    (List.range 7).map (fun d ↦
      PowerSeries.coeff d (Polynomial.toPowerSeries (c037Poly 2) + c037Tail 2)) =
      [0, 1, -1, 1, -1, 1, 0] := by
  refine ⟨by simp [c037Poly], c037Poly_empirical_values.2.1, ?_⟩
  have hN2 := (evenProd_mul_a203568Series 2 (by omega)).symm
  have heven2 : c037EvenProd 2 = 1 + (PowerSeries.X : ℤ⟦X⟧) ^ 2 := by
    unfold c037EvenProd
    have hIcc : Finset.Icc 1 (2 - 1) = {1} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_singleton]
      omega
    rw [hIcc, Finset.prod_singleton]
  have hcoeff : ∀ d : ℕ,
      PowerSeries.coeff d (Polynomial.toPowerSeries (c037Poly 2) + c037Tail 2) =
        a203568Compute d + if 2 ≤ d then a203568Compute (d - 2) else 0 := by
    intro d
    rw [hN2, heven2, add_mul, one_mul, map_add, a203568Series, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul']
    split_ifs with hd2
    · rw [PowerSeries.coeff_mk, a203568_eq_compute, a203568_eq_compute]
    · rw [a203568_eq_compute]
  simp_rw [hcoeff]
  rfl

end Mathproofs.A203568RogersFineFamily
