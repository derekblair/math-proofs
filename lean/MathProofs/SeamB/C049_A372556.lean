import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Find
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.Ring.Nat

/-!
# Seam B Entry C049 (OEIS A372556): Antti Karttunen Minimal Jacobsthal Summand Bound

Formalizes and proves Antti Karttunen's May 10, 2024 conjecture on `OEIS A372556` (`%C` line 13)
against the frozen contract `PIN-C049.md` v1 (`fidelity_notes` §1), following the repaired
exchange/potential route from `SCOPING-C049.md` §1.2:
1. The 6-identity Jacobsthal carry system `(E1)–(E6)` (`jacobsthal_E1`..`jacobsthal_E6`),
   together with a refutation witness (`triage_id2_false`) showing the naive second identity fails
   for all `k ≥ 2`.
2. Exactness of `g n = Nat.log 2 (3 * n + 1)` against `max { k | J k ≤ n }` (`J_g_le`,
   `lt_J_g_succ`, `le_g_of_J_le`).
3. Additive base-6 potential `Phi(M) = (M.map (fun k => 6 ^ k)).sum`, canonical minimal
   representations `IsCanonical`, bounded-supremum existence (`exists_canonical_min_rep`), and
   hereditary sub-multiset optimality (`IsCanonical_of_add_left`).
4. The 2-step even-barrier induction (`canonical_sum_le_pred_even_jacobsthal`): every canonical
   multiset supported on `{2, …, 2K + 1}` has `J`-sum at most `J (2K + 2) - 1`.
5. The parity refinement (`a_eq_g_of_even_g`) and the pinned theorem (`a_eq_g_or_pred`).
6. A computable bottom-up dynamic-programming mirror (`L_dp`, `a_dp`) formally proved equal to
   the pinned `noncomputable` definitions (`L_dp_eq_L`, `a_dp_eq_a`), discharging kernel-checked
   OEIS spot checks including `a 63 = 6 < g 63 = 7` (`exists_a_eq_g_pred_lt`).
-/

namespace C049

/-- Jacobsthal sequence `A001045` (`J : ℕ → ℕ`). -/
def J : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => J (k + 1) + 2 * J k

/-- Lower Jacobsthal inverse / greedy summand index `A130249` (`g : ℕ → ℕ`). -/
def g (n : ℕ) : ℕ :=
  Nat.log 2 (3 * n + 1)

/-- Existence of a Jacobsthal multiset representation for every `n : ℕ`, witnessed at `r = n`
by `M = Multiset.replicate n 2` (since `J 2 = 1`). -/
theorem h_exists (n : ℕ) : ∃ r : ℕ, ∃ M : Multiset ℕ, M.card = r ∧ (M.map J).sum = n := by
  refine ⟨n, Multiset.replicate n 2, Multiset.card_replicate n 2, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Multiset.replicate_succ, Multiset.map_cons, Multiset.sum_cons, ih]
    simp [J, Nat.add_comm]

open scoped Classical

/-- Minimum Jacobsthal summand count `A372555` (`L : ℕ → ℕ`). -/
noncomputable def L (n : ℕ) : ℕ :=
  Nat.find (h_exists n)

/-- Optimal largest summand index `A372556` (`a : ℕ → ℕ`). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (g n)).filter (fun k => ∃ M : Multiset ℕ, M.card = L n ∧ (M.map J).sum = n ∧ k ∈ M)).sup id

/-! ### Section 1: Jacobsthal Recurrence Laws and the Six-Identity Carry System `(E1)–(E6)` -/

@[simp] theorem J_zero : J 0 = 0 := rfl
@[simp] theorem J_one : J 1 = 1 := rfl
@[simp] theorem J_two : J 2 = 1 := rfl
@[simp] theorem J_three : J 3 = 3 := rfl
@[simp] theorem J_four : J 4 = 5 := rfl

theorem J_add_two (k : ℕ) : J (k + 2) = J (k + 1) + 2 * J k := rfl

/-- Alternating doubling law on `ℕ` (Step 1 of `SCOPING-C049.md` §1.2). -/
theorem J_step_pair (t : ℕ) :
    J (2 * t + 1) = 2 * J (2 * t) + 1 ∧ 2 * J (2 * t + 1) = J (2 * t + 2) + 1 := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 * t + 2 by omega]
    have h1 : J (2 * t + 2 + 1) = J (2 * t + 2) + 2 * J (2 * t + 1) := rfl
    have h2 : J (2 * t + 2 + 2) = J (2 * t + 2 + 1) + 2 * J (2 * t + 2) := rfl
    omega

/-- Parity-split closed form `3 * J (2t) + 1 = 2^(2t)` and `3 * J (2t+1) = 2^(2t+1) + 1`. -/
theorem three_mul_J_pair (t : ℕ) :
    3 * J (2 * t) + 1 = 2 ^ (2 * t) ∧ 3 * J (2 * t + 1) = 2 ^ (2 * t + 1) + 1 := by
  induction t with
  | zero => decide
  | succ t ih =>
    have hs := J_step_pair t
    have hs' := J_step_pair (t + 1)
    rw [show 2 * (t + 1) = 2 * t + 2 by omega] at hs' ⊢
    have hp1 : 2 ^ (2 * t + 2) = 4 * 2 ^ (2 * t) := by
      rw [pow_add]
      omega
    have hp2 : 2 ^ (2 * t + 2 + 1) = 2 * 2 ^ (2 * t + 2) := by
      rw [pow_succ]
      omega
    omega

theorem J_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ J k := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => decide
    | succ m =>
      rw [J_add_two]
      have := ih (by omega)
      omega

theorem J_le_succ (k : ℕ) : J k ≤ J (k + 1) := by
  cases k with
  | zero => decide
  | succ m =>
    cases m with
    | zero => decide
    | succ r =>
      have h : J (r + 1 + 1 + 1) = J (r + 1 + 1) + 2 * J (r + 1) := rfl
      omega

theorem J_mono : Monotone J :=
  monotone_nat_of_le_succ J_le_succ

/-- Refutation witness for Step 3 of `SCOPING-C049.md` §1.2: the naive Fibonacci-style identity
`2 * J k + J (k - 2) = J (k + 1) + J (k - 1)` is false for every `k ≥ 2`. -/
theorem triage_id2_false {k : ℕ} (hk : 2 ≤ k) :
    2 * J k + J (k - 2) ≠ J (k + 1) + J (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show m + 2 - 2 = m by omega, show m + 2 + 1 = m + 3 by omega,
    show m + 2 - 1 = m + 1 by omega]
  obtain ⟨t, rfl | rfl⟩ : ∃ t, m = 2 * t ∨ m = 2 * t + 1 := ⟨m / 2, by omega⟩
  · have h0 := (three_mul_J_pair t).1
    have h1 := (three_mul_J_pair t).2
    have h2 := (three_mul_J_pair (t + 1)).1
    have h3 := (three_mul_J_pair (t + 1)).2
    rw [show 2 * (t + 1) = 2 * t + 2 by omega] at h2 h3
    rw [show 2 * t + 2 + 1 = 2 * t + 3 by omega] at h3
    have hp1 : 2 ^ (2 * t + 1) = 2 * 2 ^ (2 * t) := by rw [pow_succ]; omega
    have hp2 : 2 ^ (2 * t + 2) = 4 * 2 ^ (2 * t) := by rw [pow_add]; omega
    have hp3 : 2 ^ (2 * t + 3) = 8 * 2 ^ (2 * t) := by rw [pow_add]; omega
    have hpos : 1 ≤ 2 ^ (2 * t) := Nat.one_le_pow _ _ (by omega)
    omega
  · have h0 := (three_mul_J_pair t).2
    have h1 := (three_mul_J_pair (t + 1)).1
    have h2 := (three_mul_J_pair (t + 1)).2
    have h3 := (three_mul_J_pair (t + 2)).1
    rw [show 2 * (t + 1) = 2 * t + 2 by omega] at h1 h2
    rw [show 2 * t + 2 + 1 = 2 * t + 3 by omega] at h2
    rw [show 2 * (t + 2) = 2 * t + 4 by omega] at h3
    rw [show 2 * t + 1 + 2 = 2 * t + 3 by omega, show 2 * t + 1 + 3 = 2 * t + 4 by omega,
      show 2 * t + 1 + 1 = 2 * t + 2 by omega]
    have hp1 : 2 ^ (2 * t + 2) = 2 * 2 ^ (2 * t + 1) := by rw [pow_succ]; omega
    have hp2 : 2 ^ (2 * t + 3) = 4 * 2 ^ (2 * t + 1) := by
      rw [show 2 * t + 3 = (2 * t + 1) + 2 by omega, pow_add]; omega
    have hp3 : 2 ^ (2 * t + 4) = 8 * 2 ^ (2 * t + 1) := by
      rw [show 2 * t + 4 = (2 * t + 1) + 3 by omega, pow_add]; omega
    have hpos : 2 ≤ 2 ^ (2 * t + 1) := by
      rw [pow_succ]
      have : 1 ≤ 2 ^ (2 * t) := Nat.one_le_pow _ _ (by omega)
      omega
    omega

/-- Rewrite `(E1)` (Step 2): `J k + 2 * J (k - 1) = J (k + 1)` for `k ≥ 1`. -/
theorem jacobsthal_E1 {k : ℕ} (hk : 1 ≤ k) :
    J k + 2 * J (k - 1) = J (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rfl

/-- Rewrite `(E2)` (Step 5): `2 * J (2t + 1) = J (2t + 2) + J 2`. -/
theorem jacobsthal_E2 (t : ℕ) :
    2 * J (2 * t + 1) = J (2 * t + 2) + J 2 := by
  have h := (J_step_pair t).2
  simpa [J_two] using h

/-- Rewrite `(E3)` (Step 6): `2 * J (2t) + J 2 = J (2t + 1)`. -/
theorem jacobsthal_E3 (t : ℕ) :
    2 * J (2 * t) + J 2 = J (2 * t + 1) := by
  have h := (J_step_pair t).1
  simpa [J_two] using h.symm

/-- Rewrite `(E4)` (Step 7): `4 * J (2t) + J 2 = J (2t + 2)`. -/
theorem jacobsthal_E4 (t : ℕ) :
    4 * J (2 * t) + J 2 = J (2 * t + 2) := by
  have h1 := (J_step_pair t).1
  have h2 := (J_step_pair t).2
  change 4 * J (2 * t) + 1 = J (2 * t + 2)
  omega

/-- Rewrite `(E5)` (Step 8): `4 * J (2t) + J (2u + 1) = J (2t + 2) + 2 * J (2u)`. -/
theorem jacobsthal_E5 (t u : ℕ) :
    4 * J (2 * t) + J (2 * u + 1) = J (2 * t + 2) + 2 * J (2 * u) := by
  have h4 := jacobsthal_E4 t
  have h3 := jacobsthal_E3 u
  omega

/-- Rewrite `(E6)` (Step 9): `4 * J (2t) + J (2u) = J (2t + 2) + 4 * J (2u - 2)` for `u ≥ 1`. -/
theorem jacobsthal_E6 (t : ℕ) {u : ℕ} (hu : 1 ≤ u) :
    4 * J (2 * t) + J (2 * u) = J (2 * t + 2) + 4 * J (2 * u - 2) := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  have h4t := jacobsthal_E4 t
  have h4v := jacobsthal_E4 v
  rw [show 2 * (v + 1) - 2 = 2 * v by omega, show 2 * (v + 1) = 2 * v + 2 by omega]
  omega

/-! ### Section 2: Exactness of `g`, Minimality Properties of `L`, and Bounds on `a` -/

/-- For every `n : ℕ`, `J (g n) ≤ n`. -/
theorem J_g_le (n : ℕ) : J (g n) ≤ n := by
  have hlow : 2 ^ g n ≤ 3 * n + 1 := Nat.pow_log_le_self 2 (by omega)
  obtain ⟨t, ht | ht⟩ : ∃ t, g n = 2 * t ∨ g n = 2 * t + 1 := ⟨g n / 2, by omega⟩
  · rw [ht] at hlow ⊢
    have hJ := (three_mul_J_pair t).1
    omega
  · rw [ht] at hlow ⊢
    have hJ := (three_mul_J_pair t).2
    omega

/-- For every `n : ℕ`, `n < J (g n + 1)`. -/
theorem lt_J_g_succ (n : ℕ) : n < J (g n + 1) := by
  have hhigh : 3 * n + 1 < 2 ^ (g n + 1) := Nat.lt_pow_succ_log_self (by decide) (3 * n + 1)
  obtain ⟨t, ht | ht⟩ : ∃ t, g n = 2 * t ∨ g n = 2 * t + 1 := ⟨g n / 2, by omega⟩
  · rw [ht] at hhigh ⊢
    have hJ := (three_mul_J_pair t).2
    omega
  · rw [ht, show 2 * t + 1 + 1 = 2 * t + 2 by omega] at hhigh ⊢
    have hJ := (three_mul_J_pair (t + 1)).1
    rw [show 2 * (t + 1) = 2 * t + 2 by omega] at hJ
    omega

theorem le_g_of_J_le {n k : ℕ} (h : J k ≤ n) : k ≤ g n := by
  by_contra hlt
  have hk : g n + 1 ≤ k := by omega
  have h1 : J (g n + 1) ≤ J k := J_mono hk
  have h2 : n < J (g n + 1) := lt_J_g_succ n
  omega

theorem two_le_g_of_pos {n : ℕ} (hn : 1 ≤ n) : 2 ≤ g n :=
  le_g_of_J_le (by simpa [J_two] using hn)

theorem J_le_sum_of_mem {M : Multiset ℕ} {k : ℕ} (hk : k ∈ M) :
    J k ≤ (M.map J).sum := by
  rw [← Multiset.cons_erase hk, Multiset.map_cons, Multiset.sum_cons]
  omega

theorem L_spec (n : ℕ) : ∃ M : Multiset ℕ, M.card = L n ∧ (M.map J).sum = n :=
  Nat.find_spec (h_exists n)

theorem L_le_card {n : ℕ} (M : Multiset ℕ) (hsum : (M.map J).sum = n) : L n ≤ M.card :=
  Nat.find_min' (h_exists n) ⟨M, rfl, hsum⟩

theorem zero_notMem_of_min {n : ℕ} {M : Multiset ℕ}
    (hcard : M.card = L n) (hsum : (M.map J).sum = n) : 0 ∉ M := by
  intro h0
  have hcons := Multiset.cons_erase h0
  have hsum' : ((M.erase 0).map J).sum = n := by
    have hs := congrArg (fun s => (s.map J).sum) hcons
    simp only [Multiset.map_cons, Multiset.sum_cons, J_zero, zero_add] at hs
    exact hs.trans hsum
  have hcard' : (M.erase 0).card + 1 = M.card := by
    have hc := congrArg Multiset.card hcons
    simpa [Multiset.card_cons] using hc
  have hle := L_le_card (M.erase 0) hsum'
  omega

theorem a_le_g (n : ℕ) : a n ≤ g n := by
  unfold a
  apply Finset.sup_le
  intro k hk
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2

theorem le_a_of_mem_min {n k : ℕ} {M : Multiset ℕ}
    (hcard : M.card = L n) (hsum : (M.map J).sum = n) (hk : k ∈ M) : k ≤ a n := by
  have hk0 : k ≠ 0 := fun h => zero_notMem_of_min hcard hsum (h ▸ hk)
  have hkg : k ≤ g n := le_g_of_J_le (hsum ▸ J_le_sum_of_mem hk)
  have hmem : k ∈ (Finset.Icc 1 (g n)).filter
      (fun x => ∃ M' : Multiset ℕ, M'.card = L n ∧ (M'.map J).sum = n ∧ x ∈ M') := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hkg⟩, ⟨M, hcard, hsum, hk⟩⟩
  exact Finset.le_sup (f := id) hmem

/-- Index `2` dominates index `1` (`J 1 = J 2 = 1`), so `a n` never equals `1`. -/
theorem a_ne_one (n : ℕ) : a n ≠ 1 := by
  intro ha1
  have hne : ((Finset.Icc 1 (g n)).filter
      (fun k => ∃ M : Multiset ℕ, M.card = L n ∧ (M.map J).sum = n ∧ k ∈ M)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have : a n = 0 := by simp [a, hemp]
    omega
  obtain ⟨k, hk⟩ := hne
  obtain ⟨M, hcard, hsum, hkM⟩ := (Finset.mem_filter.mp hk).2
  have hn1 : 1 ≤ n := by
    have hk0 : k ≠ 0 := fun h => zero_notMem_of_min hcard hsum (h ▸ hkM)
    have := J_pos (k := k) (by omega)
    have := J_le_sum_of_mem hkM
    omega
  have hk_le : k ≤ 1 := by
    have := le_a_of_mem_min hcard hsum hkM
    omega
  have hk1 : k = 1 := by
    have hk0 : k ≠ 0 := fun h => zero_notMem_of_min hcard hsum (h ▸ hkM)
    omega
  subst hk1
  let M' : Multiset ℕ := 2 ::ₘ M.erase 1
  have hcard' : M'.card = L n := by
    dsimp [M']
    rw [Multiset.card_cons]
    have : (1 ::ₘ M.erase 1).card = M.card := congrArg Multiset.card (Multiset.cons_erase hkM)
    rw [Multiset.card_cons] at this
    omega
  have hsum' : (M'.map J).sum = n := by
    dsimp [M']
    rw [Multiset.map_cons, Multiset.sum_cons, J_two]
    have : ((1 ::ₘ M.erase 1).map J).sum = (M.map J).sum :=
      congrArg (fun s => (s.map J).sum) (Multiset.cons_erase hkM)
    rw [Multiset.map_cons, Multiset.sum_cons, J_one] at this
    omega
  have h2le : 2 ≤ a n := le_a_of_mem_min hcard' hsum' (Multiset.mem_cons_self 2 _)
  omega

/-! ### Section 3: Base-6 Potential `Phi`, Canonical Multisets, and Hereditary Optimality -/

/-- Additive exponential potential `Φ(M) = ∑_{k ∈ M} 6^k` (Step 12 of `SCOPING-C049.md` §1.2). -/
def Phi (M : Multiset ℕ) : ℕ :=
  (M.map (fun k => 6 ^ k)).sum

@[simp] theorem Phi_zero : Phi 0 = 0 := rfl

@[simp] theorem Phi_cons (k : ℕ) (M : Multiset ℕ) :
    Phi (k ::ₘ M) = 6 ^ k + Phi M := by
  simp [Phi]

@[simp] theorem Phi_add (A B : Multiset ℕ) :
    Phi (A + B) = Phi A + Phi B := by
  simp [Phi]

@[simp] theorem Phi_replicate (c k : ℕ) :
    Phi (Multiset.replicate c k) = c * 6 ^ k := by
  simp [Phi]

@[simp] theorem J_sum_replicate (c k : ℕ) :
    ((Multiset.replicate c k).map J).sum = c * J k := by
  simp

/-- Canonical minimal Jacobsthal multiset representation (Step 12): indices `≥ 2`,
`L`-minimal for its `J`-sum, and `Phi`-maximal among all such representations. -/
def IsCanonical (M : Multiset ℕ) : Prop :=
  (∀ k ∈ M, 2 ≤ k) ∧
  M.card = L (M.map J).sum ∧
  ∀ M' : Multiset ℕ,
    (∀ k ∈ M', 2 ≤ k) →
    M'.card = M.card →
    (M'.map J).sum = (M.map J).sum →
    Phi M' ≤ Phi M

private def promoteOnes (M : Multiset ℕ) : Multiset ℕ :=
  M.map (fun k => if k = 1 then 2 else k)

private theorem promoteOnes_card (M : Multiset ℕ) :
    (promoteOnes M).card = M.card :=
  Multiset.card_map _ M

private theorem promoteOnes_J_sum (M : Multiset ℕ) :
    ((promoteOnes M).map J).sum = (M.map J).sum := by
  unfold promoteOnes
  rw [Multiset.map_map]
  congr 2
  ext k
  by_cases hk : k = 1
  · subst hk; rfl
  · simp [hk]

private theorem promoteOnes_two_le {M : Multiset ℕ} (h0 : 0 ∉ M) :
    ∀ x ∈ promoteOnes M, 2 ≤ x := by
  intro x hx
  rcases Multiset.mem_map.mp hx with ⟨k, hkM, rfl⟩
  have hk0 : k ≠ 0 := fun h => h0 (h ▸ hkM)
  by_cases hk1 : k = 1
  · simp [hk1]
  · simp [hk1]; omega

private theorem Phi_le_card_mul_pow {M : Multiset ℕ} {B : ℕ} (hB : ∀ k ∈ M, k ≤ B) :
    Phi M ≤ M.card * 6 ^ B := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Phi_cons, Multiset.card_cons, Nat.add_mul, one_mul]
    have hxB : x ≤ B := hB x (Multiset.mem_cons_self x s)
    have hpow : 6 ^ x ≤ 6 ^ B := Nat.pow_le_pow_right (by omega) hxB
    have hs : Phi s ≤ s.card * 6 ^ B := ih (fun k hk => hB k (Multiset.mem_cons_of_mem hk))
    omega

private theorem exists_max_of_bdd (P : ℕ → Prop) (UB : ℕ)
    (hne : ∃ v, v ≤ UB ∧ P v) (hbdd : ∀ v, P v → v ≤ UB) :
    ∃ vmax, P vmax ∧ ∀ v, P v → v ≤ vmax := by
  induction UB with
  | zero =>
    rcases hne with ⟨v, hv0, hvP⟩
    have hv : v = 0 := by omega
    subst hv
    exact ⟨0, hvP, hbdd⟩
  | succ u ih =>
    by_cases htop : P (u + 1)
    · exact ⟨u + 1, htop, hbdd⟩
    · have hbdd' : ∀ v, P v → v ≤ u := by
        intro v hvP
        have hle := hbdd v hvP
        have hne_top : v ≠ u + 1 := fun heq => htop (heq ▸ hvP)
        omega
      rcases hne with ⟨v, _, hvP⟩
      exact ih ⟨v, hbdd' v hvP, hvP⟩ hbdd'

/-- Step 12 (`SCOPING-C049.md` §1.2 / §3.2): Every `n : ℕ` admits a canonical minimal
Jacobsthal multiset representation. -/
theorem exists_canonical_min_rep (n : ℕ) :
    ∃ M : Multiset ℕ, (M.map J).sum = n ∧ IsCanonical M := by
  obtain ⟨M₀, hcard₀, hsum₀⟩ := L_spec n
  let M₁ := promoteOnes M₀
  have h2₁ : ∀ k ∈ M₁, 2 ≤ k := promoteOnes_two_le (zero_notMem_of_min hcard₀ hsum₀)
  have hcard₁ : M₁.card = L n := (promoteOnes_card M₀).trans hcard₀
  have hsum₁ : (M₁.map J).sum = n := (promoteOnes_J_sum M₀).trans hsum₀
  let P : ℕ → Prop := fun v =>
    ∃ M : Multiset ℕ, (∀ k ∈ M, 2 ≤ k) ∧ M.card = L n ∧ (M.map J).sum = n ∧ Phi M = v
  let UB : ℕ := L n * 6 ^ g n
  have hbdd : ∀ v, P v → v ≤ UB := by
    rintro v ⟨M, _, hcard, hsum, rfl⟩
    have hle_g : ∀ k ∈ M, k ≤ g n := fun k hk => le_g_of_J_le (hsum ▸ J_le_sum_of_mem hk)
    simpa [UB, hcard] using Phi_le_card_mul_pow hle_g
  have hne : ∃ v, v ≤ UB ∧ P v :=
    ⟨Phi M₁, hbdd (Phi M₁) ⟨M₁, h2₁, hcard₁, hsum₁, rfl⟩, ⟨M₁, h2₁, hcard₁, hsum₁, rfl⟩⟩
  obtain ⟨vmax, ⟨M, h2M, hcardM, hsumM, hphiM⟩, hmax⟩ := exists_max_of_bdd P UB hne hbdd
  refine ⟨M, hsumM, h2M, ?_, ?_⟩
  · simpa [hsumM] using hcardM
  · intro M' h2' hcard' hsum'
    have hP' : P (Phi M') := ⟨M', h2', hcard'.trans hcardM, hsum'.trans hsumM, rfl⟩
    have := hmax (Phi M') hP'
    omega

/-- Step 13 (`SCOPING-C049.md` §1.2): Hereditary optimality of sub-multisets. -/
theorem IsCanonical_of_add_left {A B : Multiset ℕ} (h : IsCanonical (A + B)) :
    IsCanonical A := by
  rcases h with ⟨h2, hcard, hmax⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    exact h2 k (Multiset.mem_add.mpr (Or.inl hk))
  · have hle : L (A.map J).sum ≤ A.card := L_le_card A rfl
    by_contra hneq
    have hlt : L (A.map J).sum < A.card := by omega
    obtain ⟨A', hcardA', hsumA'⟩ := L_spec (A.map J).sum
    have hsumAB : (((A' + B).map J).sum) = ((A + B).map J).sum := by
      simp [hsumA']
    have hL_le : L ((A + B).map J).sum ≤ (A' + B).card := L_le_card (A' + B) hsumAB
    rw [Multiset.card_add] at hL_le hcard
    omega
  · intro A' h2A' hcardA' hsumA'
    have h2AB : ∀ k ∈ A' + B, 2 ≤ k := by
      intro k hk
      rcases Multiset.mem_add.mp hk with hkA | hkB
      · exact h2A' k hkA
      · exact h2 k (Multiset.mem_add.mpr (Or.inr hkB))
    have hcardAB : (A' + B).card = (A + B).card := by simp [hcardA']
    have hsumAB : ((A' + B).map J).sum = ((A + B).map J).sum := by simp [hsumA']
    have hphi := hmax (A' + B) h2AB hcardAB hsumAB
    simp only [Phi_add] at hphi
    omega

/-- Forbidden-pattern helper for cardinality-reducing exchanges `(E1), (E3), (E4), (E5)`. -/
theorem IsCanonical_not_shorter {S B S' : Multiset ℕ}
    (hM : IsCanonical (S + B))
    (hsum : (S'.map J).sum = (S.map J).sum)
    (hcard : S'.card < S.card) : False := by
  have hS : IsCanonical S := IsCanonical_of_add_left hM
  have hL : L (S.map J).sum ≤ S'.card := L_le_card S' hsum
  have hScard : S.card = L (S.map J).sum := hS.2.1
  omega

/-- Forbidden-pattern helper for `Phi`-increasing equal-length exchanges `(E2), (E6)`. -/
theorem IsCanonical_not_Phi_gt {S B S' : Multiset ℕ}
    (hM : IsCanonical (S + B))
    (h2 : ∀ k ∈ S', 2 ≤ k)
    (hcard : S'.card = S.card)
    (hsum : (S'.map J).sum = (S.map J).sum)
    (hphi : Phi S < Phi S') : False := by
  have hS : IsCanonical S := IsCanonical_of_add_left hM
  have hle : Phi S' ≤ Phi S := hS.2.2 S' h2 hcard hsum
  omega

/-! ### Section 4: The 2-Step Even-Barrier Induction (`canonical_sum_le_pred_even_jacobsthal`) -/

private theorem multiset_decomp_eq (s : Multiset ℕ) (x : ℕ) :
    s = Multiset.replicate (s.count x) x + s.filter (· ≠ x) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons y t ih =>
    by_cases hyx : y = x
    · subst hyx
      rw [Multiset.count_cons_self, Multiset.replicate_succ, Multiset.cons_add,
        Multiset.filter_cons_of_neg _ (by simp)]
      exact congrArg (y ::ₘ ·) ih
    · have hf : Multiset.filter (· ≠ x) (y ::ₘ t) = y ::ₘ Multiset.filter (· ≠ x) t :=
        Multiset.filter_cons_of_pos t hyx
      rw [Multiset.count_cons_of_ne (Ne.symm hyx), hf, Multiset.add_cons]
      exact congrArg (y ::ₘ ·) ih

private theorem replicate_split {c d : ℕ} (h : d ≤ c) (x : ℕ) :
    Multiset.replicate c x = Multiset.replicate d x + Multiset.replicate (c - d) x := by
  rw [← Multiset.replicate_add, Nat.add_sub_cancel' h]

private theorem canonical_count_odd_le_one {K : ℕ} (_hK : 1 ≤ K) {c1 : ℕ} {B : Multiset ℕ}
    (hM : IsCanonical (Multiset.replicate c1 (2 * K + 1) + B)) : c1 ≤ 1 := by
  by_contra hc1
  have h2le : 2 ≤ c1 := by omega
  have hsplit : Multiset.replicate c1 (2 * K + 1) + B =
      Multiset.replicate 2 (2 * K + 1) + (Multiset.replicate (c1 - 2) (2 * K + 1) + B) := by
    rw [replicate_split h2le (2 * K + 1), add_assoc]
  rw [hsplit] at hM
  let S' : Multiset ℕ := (2 * K + 2) ::ₘ {2}
  have h2S' : ∀ k ∈ S', 2 ≤ k := by
    intro k hk
    rcases Multiset.mem_cons.mp hk with rfl | hk'
    · omega
    · rw [Multiset.mem_singleton.mp hk']
  have hcardS' : S'.card = (Multiset.replicate 2 (2 * K + 1)).card := rfl
  have hsumS' : (S'.map J).sum = ((Multiset.replicate 2 (2 * K + 1)).map J).sum := by
    simp only [S', Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton, J_sum_replicate]
    exact (jacobsthal_E2 K).symm
  have hphiS' : Phi (Multiset.replicate 2 (2 * K + 1)) < Phi S' := by
    simp only [S', Phi_cons, Phi_replicate]
    have hpow : 6 ^ (2 * K + 2) = 6 * 6 ^ (2 * K + 1) := by
      rw [show 2 * K + 2 = (2 * K + 1) + 1 by omega, pow_succ]
      omega
    have hpos : 1 ≤ 6 ^ (2 * K + 1) := Nat.one_le_pow _ _ (by omega)
    have h6_2 : Phi {2} = 36 := rfl
    rw [h6_2]
    omega
  exact IsCanonical_not_Phi_gt hM h2S' hcardS' hsumS' hphiS'

private theorem canonical_not_odd_and_two_even {K : ℕ} (_hK : 1 ≤ K) {c1 c0 : ℕ} {R : Multiset ℕ}
    (hM : IsCanonical (Multiset.replicate c1 (2 * K + 1) + Multiset.replicate c0 (2 * K) + R))
    (hc1 : 1 ≤ c1) : c0 ≤ 1 := by
  by_contra hc0
  have h2le : 2 ≤ c0 := by omega
  let S : Multiset ℕ := Multiset.replicate 1 (2 * K + 1) + Multiset.replicate 2 (2 * K)
  let B : Multiset ℕ :=
    Multiset.replicate (c1 - 1) (2 * K + 1) + Multiset.replicate (c0 - 2) (2 * K) + R
  have hsplit :
      Multiset.replicate c1 (2 * K + 1) + Multiset.replicate c0 (2 * K) + R = S + B := by
    dsimp [S, B]
    rw [replicate_split hc1 (2 * K + 1), replicate_split h2le (2 * K)]
    ac_rfl
  rw [hsplit] at hM
  let S' : Multiset ℕ := {2 * K + 2}
  have hsumS' : (S'.map J).sum = (S.map J).sum := by
    have hS' : (S'.map J).sum = J (2 * K + 2) := by simp [S']
    have hS : (S.map J).sum = J (2 * K + 1) + 2 * J (2 * K) := by
      simp [S]; omega
    have hE1 : J (2 * K + 2) = J (2 * K + 1) + 2 * J (2 * K) := rfl
    rw [hS', hS, hE1]
  have hcardS' : S'.card < S.card := by simp [S', S]
  exact IsCanonical_not_shorter hM hsumS' hcardS'

private theorem canonical_sum_le_aux :
    ∀ (m : ℕ) (M : Multiset ℕ),
      IsCanonical M →
      (∀ k ∈ M, k ≤ 2 * (m + 1) + 1) →
      (M.map J).sum ≤ J (2 * (m + 1) + 2) - 1
  | 0, M, hM, hsupp => by
    -- Base case `K = 1`: support of `M` lies in `{2, 3}`, target `≤ J 4 - 1 = 4`.
    let M₁ := M.filter (· ≠ 3)
    let R := M₁.filter (· ≠ 2)
    let c1 := M.count 3
    let c0 := M₁.count 2
    have hM_eq : M = Multiset.replicate c1 3 + Multiset.replicate c0 2 + R := by
      have h1 : M = Multiset.replicate c1 3 + M₁ := multiset_decomp_eq M 3
      have h2 : M₁ = Multiset.replicate c0 2 + R := multiset_decomp_eq M₁ 2
      rw [h1, h2, add_assoc]
    have hR_zero : R = 0 := by
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro r hr
      have hr1 : r ∈ M₁ ∧ r ≠ 2 := Multiset.mem_filter.mp hr
      have hr0 : r ∈ M ∧ r ≠ 3 := Multiset.mem_filter.mp hr1.1
      have h2r : 2 ≤ r := hM.1 r hr0.1
      have h3r : r ≤ 3 := hsupp r hr0.1
      omega
    rw [hR_zero, add_zero] at hM_eq
    have hM' : IsCanonical (Multiset.replicate c1 3 + Multiset.replicate c0 2) := hM_eq ▸ hM
    have hc1 : c1 ≤ 1 := by
      simpa using canonical_count_odd_le_one (K := 1) (by omega) hM'
    have hc0 : c0 ≤ 2 := by
      by_contra hc0_gt
      have h3le : 3 ≤ c0 := by omega
      have hsplit : Multiset.replicate c1 3 + Multiset.replicate c0 2 =
          Multiset.replicate 3 2 + (Multiset.replicate c1 3 + Multiset.replicate (c0 - 3) 2) := by
        rw [replicate_split h3le 2]
        ac_rfl
      rw [hsplit] at hM'
      have hsum : (({3} : Multiset ℕ).map J).sum = ((Multiset.replicate 3 2).map J).sum := by decide
      have hcard : ({3} : Multiset ℕ).card < (Multiset.replicate 3 2).card := by decide
      exact IsCanonical_not_shorter hM' hsum hcard
    have hnotboth : ¬(1 ≤ c1 ∧ 2 ≤ c0) := by
      rintro ⟨h1, h2⟩
      have hM'' : IsCanonical (Multiset.replicate c1 3 + Multiset.replicate c0 2 + 0) := by
        simpa using hM'
      have := canonical_not_odd_and_two_even (K := 1) (by omega) hM'' h1
      omega
    have hsumM : (M.map J).sum = c1 * 3 + c0 * 1 := by
      rw [hM_eq]
      simp [J_three, J_two]
    change (M.map J).sum ≤ J 4 - 1
    rw [J_four]
    omega
  | m + 1, M, hM, hsupp => by
    -- Inductive step `K = m + 2 ≥ 2`: assume `I_{m+1}` and prove `I_{m+2}`.
    let K : ℕ := m + 2
    have hK2 : 2 ≤ K := by omega
    let M₁ := M.filter (· ≠ 2 * K + 1)
    let R := M₁.filter (· ≠ 2 * K)
    let c1 := M.count (2 * K + 1)
    let c0 := M₁.count (2 * K)
    have hM_eq : M = Multiset.replicate c1 (2 * K + 1) + Multiset.replicate c0 (2 * K) + R := by
      have h1 : M = Multiset.replicate c1 (2 * K + 1) + M₁ := multiset_decomp_eq M (2 * K + 1)
      have h2 : M₁ = Multiset.replicate c0 (2 * K) + R := multiset_decomp_eq M₁ (2 * K)
      rw [h1, h2, add_assoc]
    have hR_mem : ∀ r ∈ R, 2 ≤ r ∧ r ≤ 2 * (m + 1) + 1 := by
      intro r hr
      have hr1 : r ∈ M₁ ∧ r ≠ 2 * K := Multiset.mem_filter.mp hr
      have hr0 : r ∈ M ∧ r ≠ 2 * K + 1 := Multiset.mem_filter.mp hr1.1
      have h2r : 2 ≤ r := hM.1 r hr0.1
      have htop : r ≤ 2 * K + 1 := hsupp r hr0.1
      exact ⟨h2r, by omega⟩
    have hM_canon :
        IsCanonical (Multiset.replicate c1 (2 * K + 1) + Multiset.replicate c0 (2 * K) + R) :=
      hM_eq ▸ hM
    have hR_canon : IsCanonical R := by
      have hcomm :
          Multiset.replicate c1 (2 * K + 1) + Multiset.replicate c0 (2 * K) + R =
            R + (Multiset.replicate c1 (2 * K + 1) + Multiset.replicate c0 (2 * K)) := by
        ac_rfl
      exact IsCanonical_of_add_left (hcomm ▸ hM_canon)
    have hR_ih : (R.map J).sum ≤ J (2 * K) - 1 := by
      have := canonical_sum_le_aux m R hR_canon (fun r hr => (hR_mem r hr).2)
      simpa [show 2 * (m + 1) + 2 = 2 * K by omega] using this
    have hc1 : c1 ≤ 1 := by
      have hassoc :
          Multiset.replicate c1 (2 * K + 1) + (Multiset.replicate c0 (2 * K) + R) =
            Multiset.replicate c1 (2 * K + 1) + Multiset.replicate c0 (2 * K) + R := by
        ac_rfl
      exact canonical_count_odd_le_one (K := K) (by omega) (hassoc.symm ▸ hM_canon)
    have hJ2K_pos : 1 ≤ J (2 * K) := J_pos (by omega)
    have hM_sum : (M.map J).sum = c1 * J (2 * K + 1) + c0 * J (2 * K) + (R.map J).sum := by
      rw [hM_eq]
      simp [add_assoc]
    change (M.map J).sum ≤ J (2 * K + 2) - 1
    by_cases hc1_pos : c1 = 1
    · -- Case 15a (`c_{2K+1} = 1`): `(E1)` forces `c_{2K} ≤ 1`.
      have hc0_le : c0 ≤ 1 :=
        canonical_not_odd_and_two_even (K := K) (by omega) hM_canon (by omega)
      have hE1 : J (2 * K + 1) + 2 * J (2 * K) = J (2 * K + 2) := rfl
      have hc0_mul : c0 * J (2 * K) ≤ 1 * J (2 * K) := Nat.mul_le_mul_right _ hc0_le
      rw [hM_sum, hc1_pos]
      omega
    · have hc1_zero : c1 = 0 := by omega
      have hE4 : 4 * J (2 * K) + 1 = J (2 * K + 2) := by
        simpa [J_two] using jacobsthal_E4 K
      by_cases hc0_le3 : c0 ≤ 3
      · -- Case 15b (`c_{2K+1} = 0` and `c_{2K} ≤ 3`).
        have hc0_mul : c0 * J (2 * K) ≤ 3 * J (2 * K) := Nat.mul_le_mul_right _ hc0_le3
        rw [hM_sum, hc1_zero]
        omega
      · -- Case 16 (`c_{2K+1} = 0` and `c_{2K} ≥ 4`): `(E6)` forbids `c0 ≥ 5`, and `c0 = 4 → R = 0`.
        have hc0_le4 : c0 ≤ 4 := by
          by_contra hc0_ge5
          have h5le : 5 ≤ c0 := by omega
          set S : Multiset ℕ := Multiset.replicate 5 (2 * K) with hS_def
          set B : Multiset ℕ :=
            Multiset.replicate c1 (2 * K + 1) + Multiset.replicate (c0 - 5) (2 * K) + R with hB_def
          have hsplit :
              Multiset.replicate c1 (2 * K + 1) + Multiset.replicate c0 (2 * K) + R = S + B := by
            rw [hS_def, hB_def, replicate_split h5le (2 * K)]
            ac_rfl
          set S' : Multiset ℕ := (2 * K + 2) ::ₘ Multiset.replicate 4 (2 * K - 2) with hS'_def
          have h2S' : ∀ k ∈ S', 2 ≤ k := by
            intro k hk
            rw [hS'_def] at hk
            rcases Multiset.mem_cons.mp hk with rfl | hk'
            · omega
            · have := Multiset.eq_of_mem_replicate hk'
              omega
          have hcardS' : S'.card = S.card := by simp [hS'_def, hS_def]
          have hsumS' : (S'.map J).sum = (S.map J).sum := by
            rw [hS'_def, hS_def]
            simp only [Multiset.map_cons, Multiset.sum_cons, J_sum_replicate]
            have hE6 := jacobsthal_E6 K (u := K) (by omega)
            omega
          have hphiS' : Phi S < Phi S' := by
            rw [hS'_def, hS_def]
            simp only [Phi_cons, Phi_replicate]
            have hpow : 6 ^ (2 * K + 2) = 36 * 6 ^ (2 * K) := by
              rw [pow_add]
              omega
            have hpos : 1 ≤ 6 ^ (2 * K) := Nat.one_le_pow _ _ (by omega)
            omega
          exact IsCanonical_not_Phi_gt (hsplit ▸ hM_canon) h2S' hcardS' hsumS' hphiS'
        have hc0_eq4 : c0 = 4 := by omega
        have hR_empty : R = 0 := by
          rw [Multiset.eq_zero_iff_forall_notMem]
          intro r hr
          obtain ⟨hr_lo, hr_hi⟩ := hR_mem r hr
          set S : Multiset ℕ := Multiset.replicate 4 (2 * K) + {r} with hS_def
          set B : Multiset ℕ := Multiset.replicate c1 (2 * K + 1) + R.erase r with hB_def
          have hsplit :
              Multiset.replicate c1 (2 * K + 1) + Multiset.replicate c0 (2 * K) + R = S + B := by
            have hr_eq : R = {r} + R.erase r := by
              rw [Multiset.singleton_add, Multiset.cons_erase hr]
            rw [hS_def, hB_def, hc0_eq4]
            conv_lhs => rw [hr_eq]
            ac_rfl
          have hSB : IsCanonical (S + B) := hsplit ▸ hM_canon
          obtain ⟨u, rfl | rfl⟩ : ∃ u, r = 2 * u ∨ r = 2 * u + 1 := ⟨r / 2, by omega⟩
          · -- Even `r = 2 * u` (`1 ≤ u ≤ K - 1`): `u = 1` violates `(E4)`; `u ≥ 2` violates `(E6)`.
            by_cases hu1 : u = 1
            · subst hu1
              set S' : Multiset ℕ := {2 * K + 2} with hS'_def
              have hsumS' : (S'.map J).sum = (S.map J).sum := by
                rw [hS'_def, hS_def]
                simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_add,
                  Multiset.sum_add, J_sum_replicate]
                exact (jacobsthal_E4 K).symm
              have hcardS' : S'.card < S.card := by simp [hS'_def, hS_def]
              exact IsCanonical_not_shorter hSB hsumS' hcardS'
            · have hu2 : 2 ≤ u := by omega
              set S' : Multiset ℕ := (2 * K + 2) ::ₘ Multiset.replicate 4 (2 * u - 2) with hS'_def
              have h2S' : ∀ k ∈ S', 2 ≤ k := by
                intro k hk
                rw [hS'_def] at hk
                rcases Multiset.mem_cons.mp hk with rfl | hk'
                · omega
                · have := Multiset.eq_of_mem_replicate hk'
                  omega
              have hcardS' : S'.card = S.card := by simp [hS'_def, hS_def]
              have hsumS' : (S'.map J).sum = (S.map J).sum := by
                rw [hS'_def, hS_def]
                simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_add,
                  Multiset.sum_add, J_sum_replicate, Multiset.map_singleton, Multiset.sum_singleton]
                exact (jacobsthal_E6 K (u := u) (by omega)).symm
              have hphiS' : Phi S < Phi S' := by
                have hphi_sing : Phi {2 * u} = 6 ^ (2 * u) := by simp [Phi]
                rw [hS'_def, hS_def]
                simp only [Phi_cons, Phi_add, Phi_replicate, hphi_sing]
                have hpow_le : 6 ^ (2 * u) ≤ 6 ^ (2 * K) :=
                  Nat.pow_le_pow_right (by omega) (by omega)
                have hpow_top : 6 ^ (2 * K + 2) = 36 * 6 ^ (2 * K) := by
                  rw [pow_add]
                  omega
                have hpos : 1 ≤ 6 ^ (2 * K) := Nat.one_le_pow _ _ (by omega)
                omega
              exact IsCanonical_not_Phi_gt hSB h2S' hcardS' hsumS' hphiS'
          · -- Odd `r = 2 * u + 1` (`1 ≤ u ≤ K - 1`): violates `(E5)` (`5 → 3`).
            set S' : Multiset ℕ := (2 * K + 2) ::ₘ Multiset.replicate 2 (2 * u) with hS'_def
            have hsumS' : (S'.map J).sum = (S.map J).sum := by
              rw [hS'_def, hS_def]
              simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_add,
                Multiset.sum_add, J_sum_replicate, Multiset.map_singleton, Multiset.sum_singleton]
              exact (jacobsthal_E5 K u).symm
            have hcardS' : S'.card < S.card := by simp [hS'_def, hS_def]
            exact IsCanonical_not_shorter hSB hsumS' hcardS'
        rw [hM_sum, hc1_zero, hc0_eq4, hR_empty]
        simp only [zero_mul, zero_add, Multiset.map_zero, Multiset.sum_zero, add_zero]
        omega

/-- Hardest lemma (`SCOPING-C049.md` §3.2, Steps 14–16): For every `K ≥ 1`, any canonical
minimal Jacobsthal multiset `M` supported on `{2, …, 2K + 1}` has `(M.map J).sum ≤ J (2K + 2) - 1`. -/
theorem canonical_sum_le_pred_even_jacobsthal {K : ℕ} (hK : 1 ≤ K) {M : Multiset ℕ}
    (hcanon : IsCanonical M) (hsupp : ∀ k ∈ M, k ≤ 2 * K + 1) :
    (M.map J).sum ≤ J (2 * K + 2) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  exact canonical_sum_le_aux m M hcanon hsupp

/-! ### Section 5: Parity Refinement (`PIN-C049` Q1) and Main Pinned Theorem (`a_eq_g_or_pred`) -/

/-- Parity refinement (`PIN-C049.md` Q1 / Step 17): whenever `g n` is even (`∃ t, g n = 2 * t`),
`a n = g n`. -/
theorem a_eq_g_of_even_g (n : ℕ) (heven : Even (g n)) : a n = g n := by
  have ha_le : a n ≤ g n := a_le_g n
  rcases heven with ⟨t, ht⟩
  rw [← two_mul] at ht
  cases t with
  | zero => omega
  | succ m =>
    obtain ⟨M, hsum, hcanon⟩ := exists_canonical_min_rep n
    have hcard : M.card = L n := by simpa [hsum] using hcanon.2.1
    have hn_ge : J (g n) ≤ n := J_g_le n
    cases m with
    | zero =>
      -- `g n = 2` (`n = 1` or `n = 2`)
      have hn1 : 1 ≤ n := by
        rw [ht] at hn_ge
        simpa using hn_ge
      have hne : M ≠ 0 := by
        intro h0
        rw [h0] at hsum
        simp at hsum
        omega
      obtain ⟨k, hkM⟩ := Multiset.exists_mem_of_ne_zero hne
      have hk2 : 2 ≤ k := hcanon.1 k hkM
      have hka : k ≤ a n := le_a_of_mem_min hcard hsum hkM
      omega
    | succ r =>
      -- `g n = 2 * (r + 1) + 2` (`K = r + 1 ≥ 1`)
      let K : ℕ := r + 1
      have hgn : g n = 2 * K + 2 := by dsimp [K]; omega
      have hJK_pos : 1 ≤ J (2 * K + 2) := J_pos (by omega)
      have hn_ge' : J (2 * K + 2) ≤ n := hgn ▸ hn_ge
      have hex : ∃ k ∈ M, 2 * K + 2 ≤ k := by
        by_contra hall
        have hsupp : ∀ k ∈ M, k ≤ 2 * K + 1 := by
          intro k hk
          by_contra hgt
          exact hall ⟨k, hk, by omega⟩
        have hle := canonical_sum_le_pred_even_jacobsthal (K := K) (by omega) hcanon hsupp
        omega
      obtain ⟨k, hkM, hk_lo⟩ := hex
      have hka : k ≤ a n := le_a_of_mem_min hcard hsum hkM
      omega

/-- Karttunen's May 10, 2024 conjecture (`C049`, `OEIS A372556` `%C` line 13). -/
theorem a_eq_g_or_pred : ∀ n : ℕ, a n = g n ∨ a n = g n - 1 := by
  intro n
  have ha_le : a n ≤ g n := a_le_g n
  obtain ⟨t, ht | ht⟩ : ∃ t, g n = 2 * t ∨ g n = 2 * t + 1 := ⟨g n / 2, by omega⟩
  · exact Or.inl (a_eq_g_of_even_g n ⟨t, by omega⟩)
  · -- Odd `g n = 2 * t + 1`
    have hn_ge : J (2 * t + 1) ≤ n := ht ▸ J_g_le n
    have hn_lt : n < J (2 * t + 2) := by
      have := lt_J_g_succ n
      simpa [ht] using this
    cases t with
    | zero =>
      -- `g n = 1` is impossible since `J 1 = 1` and `J 2 = 1` (`1 ≤ n < 1`).
      simp [J_one, J_two] at hn_ge hn_lt
      omega
    | succ m =>
      obtain ⟨M, hsum, hcanon⟩ := exists_canonical_min_rep n
      have hcard : M.card = L n := by simpa [hsum] using hcanon.2.1
      cases m with
      | zero =>
        -- `g n = 3` (`n = 3` or `n = 4`): canonical `M` is nonempty with elements `≥ 2 = g n - 1`.
        have hn1 : 1 ≤ n := by simp [J_three] at hn_ge; omega
        have hne : M ≠ 0 := by
          intro h0
          rw [h0] at hsum
          simp at hsum
          omega
        obtain ⟨k, hkM⟩ := Multiset.exists_mem_of_ne_zero hne
        have hk2 : 2 ≤ k := hcanon.1 k hkM
        have hka : k ≤ a n := le_a_of_mem_min hcard hsum hkM
        omega
      | succ r =>
        -- `g n = 2 * K + 3` (`K = r + 1 ≥ 1`): `I_K` forces `∃ k ∈ M, 2K + 2 ≤ k`.
        let K : ℕ := r + 1
        have hgn : g n = 2 * K + 3 := by dsimp [K]; omega
        have hJK_pos : 1 ≤ J (2 * K + 2) := J_pos (by omega)
        have hJK_le : J (2 * K + 2) ≤ n := by
          have hmono : J (2 * K + 2) ≤ J (2 * K + 3) := J_mono (by omega)
          have hn_ge' : J (2 * K + 3) ≤ n := by simpa [K, show 2 * (r + 1) + 3 = 2 * (r + 2) + 1 by omega] using hn_ge
          omega
        have hex : ∃ k ∈ M, 2 * K + 2 ≤ k := by
          by_contra hall
          have hsupp : ∀ k ∈ M, k ≤ 2 * K + 1 := by
            intro k hk
            by_contra hgt
            exact hall ⟨k, hk, by omega⟩
          have hle := canonical_sum_le_pred_even_jacobsthal (K := K) (by omega) hcanon hsupp
          omega
        obtain ⟨k, hkM, hk_lo⟩ := hex
        have hka : k ≤ a n := le_a_of_mem_min hcard hsum hkM
        omega

/-! ### Section 6: Verified Computable DP Mirror (`PIN-C049` Q2) & Kernel Spot Checks -/

/-- Bellman upper bound: for `J k ≤ n`, `L n ≤ L (n - J k) + 1`. -/
theorem L_le_succ_sub {n k : ℕ} (hJk : J k ≤ n) : L n ≤ L (n - J k) + 1 := by
  obtain ⟨M', hcard', hsum'⟩ := L_spec (n - J k)
  have hsum : (((k ::ₘ M').map J).sum) = n := by
    rw [Multiset.map_cons, Multiset.sum_cons, hsum']
    omega
  have hle := L_le_card (k ::ₘ M') hsum
  simpa [Multiset.card_cons, hcard'] using hle

/-- Bellman characterization of membership in an `L n`-minimal multiset (`n ≥ 1`). -/
theorem mem_min_iff_bellman {n k : ℕ} (hn : 1 ≤ n) (hk : k ∈ Finset.Icc 1 (g n)) :
    (∃ M : Multiset ℕ, M.card = L n ∧ (M.map J).sum = n ∧ k ∈ M) ↔ L (n - J k) + 1 = L n := by
  have hk_bounds := Finset.mem_Icc.mp hk
  have hJk : J k ≤ n := by
    by_cases hk1 : k = 1
    · subst hk1; simpa [J_one] using hn
    · exact (J_mono hk_bounds.2).trans (J_g_le n)
  constructor
  · rintro ⟨M, hcard, hsum, hkM⟩
    have hsum' : (((M.erase k).map J).sum) = n - J k := by
      have := congrArg (fun s => (s.map J).sum) (Multiset.cons_erase hkM)
      simp only [Multiset.map_cons, Multiset.sum_cons] at this
      omega
    have hcard' : (M.erase k).card + 1 = L n := by
      have := congrArg Multiset.card (Multiset.cons_erase hkM)
      simp only [Multiset.card_cons] at this
      omega
    have h1 := L_le_card (M.erase k) hsum'
    have h2 := L_le_succ_sub hJk
    omega
  · intro hbell
    obtain ⟨M', hcard', hsum'⟩ := L_spec (n - J k)
    refine ⟨k ::ₘ M', ?_, ?_, Multiset.mem_cons_self k M'⟩
    · rw [Multiset.card_cons, hcard', hbell]
    · rw [Multiset.map_cons, Multiset.sum_cons, hsum']
      omega

theorem exists_bellman_witness {n : ℕ} (hn : 1 ≤ n) :
    ∃ k ∈ Finset.Icc 1 (g n), L (n - J k) + 1 = L n := by
  obtain ⟨M, hcard, hsum⟩ := L_spec n
  have hne : M ≠ 0 := by
    intro h0
    rw [h0] at hsum
    simp at hsum
    omega
  obtain ⟨k, hkM⟩ := Multiset.exists_mem_of_ne_zero hne
  have hk0 : k ≠ 0 := fun h => zero_notMem_of_min hcard hsum (h ▸ hkM)
  have hkg : k ≤ g n := le_g_of_J_le (hsum ▸ J_le_sum_of_mem hkM)
  have hkIcc : k ∈ Finset.Icc 1 (g n) := Finset.mem_Icc.mpr ⟨by omega, hkg⟩
  exact ⟨k, hkIcc, (mem_min_iff_bellman hn hkIcc).mp ⟨M, hcard, hsum, hkM⟩⟩

@[simp] theorem L_zero : L 0 = 0 := by
  have h : L 0 ≤ (0 : Multiset ℕ).card := L_le_card (n := 0) 0 rfl
  simpa using h

@[simp] theorem a_zero : a 0 = 0 := by
  have h := a_le_g 0
  have hg0 : g 0 = 0 := rfl
  omega

/-- Scan `k = 1..s` over a reversed DP table `rev = [L (m-1), ..., L 0]`, where
`L (m - J k)` sits at index `(m - 1) - (m - J k) = J k - 1`. -/
def minPrevRev (rev : List ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => rev.getD (J 1 - 1) 0
  | k + 2 => min (rev.getD (J (k + 2) - 1) 0) (minPrevRev rev (k + 1))

/-- Tail-recursive bottom-up builder for `[L (idx + rem), ..., L 0]`. -/
def dpLoop (idx rem : ℕ) (rev : List ℕ) : List ℕ :=
  match rem with
  | 0 => rev
  | rem' + 1 =>
    let v := Nat.add (minPrevRev rev (g (idx + 1))) 1
    if Nat.beq v v then dpLoop (Nat.add idx 1) rem' (v :: rev) else rev

/-- Reversed table `[L n, L (n - 1), ..., L 0]`. -/
def revTable (n : ℕ) : List ℕ :=
  dpLoop 0 n [0]

/-- Computable DP mirror of `C049.L` (`A372555`). -/
def L_dp (n : ℕ) : ℕ :=
  (revTable n).headD 0

/-- Downward scan `k = s, ..., 1` selecting the largest `k` with `L (m - J k) + 1 = target`. -/
def maxIdxRev (rev : List ℕ) (target : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if rev.getD (J (k + 1) - 1) 0 + 1 = target then k + 1
    else maxIdxRev rev target k

/-- Computable DP mirror of `C049.a` (`A372556`). -/
def a_dp (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | m + 1 =>
    let rev := revTable m
    let ln := Nat.add (minPrevRev rev (g (m + 1))) 1
    maxIdxRev rev ln (g (m + 1))

private theorem minPrevRev_spec {rev : List ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hrev : ∀ j < m, rev.getD j 0 = L (m - 1 - j)) :
    ∀ {s : ℕ}, 1 ≤ s → s ≤ g m →
      (∀ k, 1 ≤ k → k ≤ s → minPrevRev rev s ≤ L (m - J k)) ∧
      (∃ k, 1 ≤ k ∧ k ≤ s ∧ minPrevRev rev s = L (m - J k)) := by
  intro s hs1 hsg
  induction s with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero =>
      have hlookup : rev.getD (J 1 - 1) 0 = L (m - J 1) := by
        rw [J_one, hrev 0 (by omega)]
        congr 1
      refine ⟨?_, ⟨1, le_rfl, le_rfl, hlookup⟩⟩
      intro k hk1 hk_le
      have hk_eq : k = 1 := by omega
      subst hk_eq
      change rev.getD (J 1 - 1) 0 ≤ L (m - J 1)
      omega
    | succ q =>
      obtain ⟨ih_le, ⟨k₀, hk₀1, hk₀_le, ih_eq⟩⟩ := ih (by omega) (by omega)
      have hJq_pos : 1 ≤ J (q + 2) := J_pos (by omega)
      have hJq_le : J (q + 2) ≤ m := (J_mono hsg).trans (J_g_le m)
      have hlookup : rev.getD (J (q + 2) - 1) 0 = L (m - J (q + 2)) := by
        rw [hrev (J (q + 2) - 1) (by omega)]
        congr 1
        omega
      change (∀ k, 1 ≤ k → k ≤ q + 2 →
          min (rev.getD (J (q + 2) - 1) 0) (minPrevRev rev (q + 1)) ≤ L (m - J k)) ∧
        (∃ k, 1 ≤ k ∧ k ≤ q + 2 ∧
          min (rev.getD (J (q + 2) - 1) 0) (minPrevRev rev (q + 1)) = L (m - J k))
      rw [hlookup, min_def]
      split_ifs with hcmp
      · refine ⟨?_, ⟨q + 2, by omega, le_rfl, rfl⟩⟩
        intro k hk1 hk_le
        by_cases htop : k = q + 2
        · subst htop; exact le_rfl
        · exact hcmp.trans (ih_le k hk1 (by omega))
      · refine ⟨?_, ⟨k₀, hk₀1, by omega, ih_eq⟩⟩
        intro k hk1 hk_le
        by_cases htop : k = q + 2
        · subst htop; omega
        · exact ih_le k hk1 (by omega)

private theorem minPrevRev_add_one_eq_L {rev : List ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hrev : ∀ j < m, rev.getD j 0 = L (m - 1 - j)) :
    minPrevRev rev (g m) + 1 = L m := by
  have hgm : 1 ≤ g m := le_trans (by omega) (two_le_g_of_pos hm)
  obtain ⟨hle, ⟨k₁, hk₁_lo, hk₁_hi, heq⟩⟩ := minPrevRev_spec hm hrev hgm le_rfl
  obtain ⟨k₂, hk₂_Icc, hbell₂⟩ := exists_bellman_witness hm
  rcases Finset.mem_Icc.mp hk₂_Icc with ⟨hk₂_lo, hk₂_hi⟩
  have h1 : minPrevRev rev (g m) ≤ L (m - J k₂) := hle k₂ hk₂_lo hk₂_hi
  have hJk₁ : J k₁ ≤ m := by
    by_cases hk1 : k₁ = 1
    · subst hk1; simpa [J_one] using hm
    · exact (J_mono hk₁_hi).trans (J_g_le m)
  have h2 : L m ≤ L (m - J k₁) + 1 := L_le_succ_sub hJk₁
  omega

private theorem dpLoop_spec (idx rem : ℕ) (rev : List ℕ)
    (hrev : ∀ j < idx + 1, rev.getD j 0 = L (idx - j)) :
    ∀ j < idx + rem + 1, (dpLoop idx rem rev).getD j 0 = L (idx + rem - j) := by
  induction rem generalizing idx rev with
  | zero =>
    unfold dpLoop
    simpa using hrev
  | succ rem' ih =>
    unfold dpLoop
    have hbeq : Nat.beq (Nat.add (minPrevRev rev (g (idx + 1))) 1)
        (Nat.add (minPrevRev rev (g (idx + 1))) 1) = true := Nat.beq_refl _
    simp only [hbeq, ↓reduceIte]
    have hv : Nat.add (minPrevRev rev (g (idx + 1))) 1 = L (idx + 1) :=
      minPrevRev_add_one_eq_L (m := idx + 1) (by omega) (by
        intro j hj
        simpa [show idx + 1 - 1 - j = idx - j by omega] using hrev j hj)
    have hnext : ∀ j < (idx + 1) + 1,
        (Nat.add (minPrevRev rev (g (idx + 1))) 1 :: rev).getD j 0 = L ((idx + 1) - j) := by
      intro j hj
      cases j with
      | zero => simpa [List.getD] using hv
      | succ j' =>
        simp only [List.getD, List.getElem?_cons_succ]
        simpa [show idx + 1 - (j' + 1) = idx - j' by omega] using hrev j' (by omega)
    intro j hj
    have := ih (idx + 1) _ hnext j (by omega)
    simpa [Nat.add_eq, show idx + 1 + rem' = idx + (rem' + 1) by omega] using this

theorem revTable_getD (n : ℕ) {j : ℕ} (hj : j < n + 1) :
    (revTable n).getD j 0 = L (n - j) := by
  have h0 : ∀ i < 0 + 1, ([0] : List ℕ).getD i 0 = L (0 - i) := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp [L_zero]
  simpa [revTable] using dpLoop_spec 0 n [0] h0 j (by omega)

/-- Formal equivalence of computable `L_dp` and pinned `noncomputable` `L`. -/
theorem L_dp_eq_L (n : ℕ) : L_dp n = L n := by
  have h := revTable_getD n (j := 0) (by omega)
  unfold L_dp
  cases hlist : revTable n with
  | nil =>
    rw [hlist] at h
    simpa using h
  | cons hd tl =>
    rw [hlist] at h
    simpa using h

private theorem maxIdxRev_spec {rev : List ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hrev : ∀ j < m, rev.getD j 0 = L (m - 1 - j)) :
    ∀ s ≤ g m,
      maxIdxRev rev (L m) s =
        ((Finset.Icc 1 s).filter (fun k => L (m - J k) + 1 = L m)).sup id := by
  intro s hsg
  induction s with
  | zero =>
    simp [maxIdxRev]
  | succ k ih =>
    have hJk_pos : 1 ≤ J (k + 1) := J_pos (by omega)
    have hJk_le : J (k + 1) ≤ m := by
      by_cases hk0 : k = 0
      · subst hk0; simpa [J_one] using hm
      · exact (J_mono hsg).trans (J_g_le m)
    have hlookup : rev.getD (J (k + 1) - 1) 0 = L (m - J (k + 1)) := by
      rw [hrev (J (k + 1) - 1) (by omega)]
      congr 1
      omega
    have hIcc_split : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    unfold maxIdxRev
    rw [hlookup, hIcc_split, Finset.filter_insert]
    split_ifs with hbell
    · rw [Finset.sup_insert]
      have hsup_le : ((Finset.Icc 1 k).filter (fun x => L (m - J x) + 1 = L m)).sup id ≤ k + 1 := by
        apply Finset.sup_le
        intro x hx
        have hxIcc := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).2
        dsimp [id]
        omega
      exact (sup_eq_left.mpr hsup_le).symm
    · exact ih (by omega)

/-- Formal equivalence of computable `a_dp` and pinned `noncomputable` `a`. -/
theorem a_dp_eq_a (n : ℕ) : a_dp n = a n := by
  cases n with
  | zero => simp [a_dp, a_zero]
  | succ m =>
    have hm1 : 1 ≤ m + 1 := by omega
    have hrev : ∀ j < m + 1, (revTable m).getD j 0 = L ((m + 1) - 1 - j) := by
      intro j hj
      simpa using revTable_getD m hj
    have hln : Nat.add (minPrevRev (revTable m) (g (m + 1))) 1 = L (m + 1) :=
      minPrevRev_add_one_eq_L hm1 hrev
    unfold a_dp a
    dsimp only
    rw [hln, maxIdxRev_spec hm1 hrev (g (m + 1)) le_rfl]
    congr 1
    apply Finset.filter_congr
    intro k hk
    exact (mem_min_iff_bellman hm1 hk).symm

/-! ### Kernel-Checked OEIS Non-Vacuity Spot Checks (`b372556.txt` / `b372555.txt` / `A372558`) -/

theorem spot_check_0 : g 0 = 0 ∧ L 0 = 0 ∧ a 0 = 0 := by
  rw [← L_dp_eq_L, ← a_dp_eq_a]; exact ⟨rfl, rfl, rfl⟩

theorem spot_check_1 : g 1 = 2 ∧ L 1 = 1 ∧ a 1 = 2 := by
  rw [← L_dp_eq_L, ← a_dp_eq_a]; exact ⟨rfl, rfl, rfl⟩

theorem spot_check_2 : g 2 = 2 ∧ L 2 = 2 ∧ a 2 = 2 := by
  rw [← L_dp_eq_L, ← a_dp_eq_a]; exact ⟨rfl, rfl, rfl⟩

theorem spot_check_3 : g 3 = 3 ∧ L 3 = 1 ∧ a 3 = 3 := by
  rw [← L_dp_eq_L, ← a_dp_eq_a]; exact ⟨rfl, rfl, rfl⟩

theorem spot_check_4 : g 4 = 3 ∧ L 4 = 2 ∧ a 4 = 3 := by
  rw [← L_dp_eq_L, ← a_dp_eq_a]; exact ⟨rfl, rfl, rfl⟩

/-- First `A372558` drop (`n = 63 = 21 + 21 + 21`): `a 63 = 6 = g 63 - 1 < 7 = g 63`. -/
theorem spot_check_63 : g 63 = 7 ∧ L 63 = 3 ∧ a 63 = 6 := by
  rw [← L_dp_eq_L, ← a_dp_eq_a]; exact ⟨rfl, rfl, rfl⟩

/-- Second `A372558` drop (`n = 84 = 21 + 21 + 21 + 21`): `a 84 = 6 = g 84 - 1 < 7 = g 84`. -/
theorem spot_check_84 : g 84 = 7 ∧ L 84 = 4 ∧ a 84 = 6 := by
  rw [← L_dp_eq_L, ← a_dp_eq_a]; exact ⟨rfl, rfl, rfl⟩

/-- Direct `(E6)` upgrade witness (`n = 105 = 5 * 21 = 85 + 4 * 5`): `a 105 = 8 = g 105`. -/
theorem spot_check_105 : g 105 = 8 ∧ L 105 = 5 ∧ a 105 = 8 := by
  rw [← L_dp_eq_L, ← a_dp_eq_a]; exact ⟨rfl, rfl, rfl⟩

/-- Non-vacuity of the `g n - 1` disjunct (`OEIS A372558` is nonempty), proved in the kernel. -/
theorem exists_a_eq_g_pred_lt : ∃ n : ℕ, a n = g n - 1 ∧ a n < g n := by
  refine ⟨63, ?_, ?_⟩
  · rw [spot_check_63.2.2, spot_check_63.1]
  · rw [spot_check_63.2.2, spot_check_63.1]; omega

end C049
