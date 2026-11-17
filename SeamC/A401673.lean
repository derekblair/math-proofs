import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.Ring

/-!
# Seam C Entry S017 (OEIS A401673): Dawid Ryłko's King-Graph Domicule Top-Two Diagonal-Count Conjectures

Formalizes and proves Dawid Ryłko's conjectures on `OEIS A401673` (`%F` line 17, Nov 01 2026;
live revision `#9`, Nov 09 2026 17:52:57) and companions `OEIS A239273` (`%I #51`, Nov 11 2026)
and `OEIS A011379` (`%I #207`, Nov 26 2025) against the frozen target contract `PIN-S017.md` v1
(`delta_vs_source: NONE`), following the induction-free seven-step coordinate-sum / four-class
parity route from `SCOPING-S017.md` (§2.1, Steps 1–7).
-/

namespace SeamC.A401673

open scoped BigOperators

/-! ### Pinned Target Definitions (`PIN-S017.md` v1) -/

/-- The `2n × 2n` square grid of unit cells (`OEIS A401673` `%N` line 10). -/
abbrev Board (n : ℕ) : Type := Fin (2 * n) × Fin (2 * n)

/-- Two distinct cells share a side or a corner (chessboard king distance `1`). -/
def kingAdj (n : ℕ) (u v : Board n) : Prop :=
  u ≠ v ∧ Nat.dist u.1.val v.1.val ≤ 1 ∧ Nat.dist u.2.val v.2.val ≤ 1

/-- Two cells share only a corner (diagonal domicule). -/
def diagAdj (n : ℕ) (u v : Board n) : Prop :=
  Nat.dist u.1.val v.1.val = 1 ∧ Nat.dist u.2.val v.2.val = 1

/-- `M` is a perfect matching of the `2n × 2n` king graph: vertex-disjoint domicules covering
`Board n`, with crossing diagonals in a `2 × 2` block permitted (`%e` line 24). -/
def IsDomiculeTiling (n : ℕ) (M : Finset (Sym2 (Board n))) : Prop :=
  (∀ e ∈ M, ¬ e.IsDiag ∧ ∀ u v, e = s(u, v) → kingAdj n u v) ∧
    (∀ v : Board n, ∃! e, e ∈ M ∧ v ∈ e)

/-- Predicate for a diagonal domicule (`OEIS A401673` `%C` line 11). -/
def IsDiagDomicule (n : ℕ) (e : Sym2 (Board n)) : Prop :=
  ∃ u v, e = s(u, v) ∧ diagAdj n u v

open scoped Classical in
/-- `T(n, k)` (`OEIS A401673` `%N` line 10, `%o` line 27): the number of domicule tilings of the
`2n × 2n` square with **exactly `2 * k`** diagonal domicules. -/
noncomputable def domiculeTilings (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Sym2 (Board n)))).filter (fun M =>
    IsDomiculeTiling n M ∧ (M.filter (IsDiagDomicule n)).card = 2 * k)).card

/-- Companion sequence `OEIS A011379` (`%N` line 10): `a(n) = n^2 * (n + 1)`. -/
def A011379 (n : ℕ) : ℕ := n ^ 2 * (n + 1)

/-! ### Section 1: `Nat.dist`, `Sym2`, and Matching–Involution Correspondence -/

private theorem nat_dist_def (a b : ℕ) : Nat.dist a b = (a - b) + (b - a) := rfl

private theorem kingAdj_symm {n : ℕ} {u v : Board n} (h : kingAdj n u v) : kingAdj n v u :=
  ⟨h.1.symm, by rw [Nat.dist_comm]; exact h.2.1, by rw [Nat.dist_comm]; exact h.2.2⟩

private theorem diagAdj_symm {n : ℕ} {u v : Board n} (h : diagAdj n u v) : diagAdj n v u :=
  ⟨by rw [Nat.dist_comm]; exact h.1, by rw [Nat.dist_comm]; exact h.2⟩

private theorem diagAdj_imp_kingAdj {n : ℕ} {u v : Board n} (h : diagAdj n u v) : kingAdj n u v := by
  refine ⟨?_, le_of_eq h.1, le_of_eq h.2⟩
  intro heq
  subst heq
  have h1 := h.1
  rw [nat_dist_def] at h1
  omega

private theorem edge_valid_mk {n : ℕ} {u v : Board n} (h : kingAdj n u v) :
    ¬ (s(u, v) : Sym2 (Board n)).IsDiag ∧ ∀ u' v', s(u, v) = s(u', v') → kingAdj n u' v' := by
  refine ⟨by rw [Sym2.mk_isDiag_iff]; exact h.1, ?_⟩
  intro u' v' heq
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · exact kingAdj_symm h

private theorem isDiagDomicule_mk {n : ℕ} (u v : Board n) :
    IsDiagDomicule n s(u, v) ↔ diagAdj n u v := by
  constructor
  · rintro ⟨u', v', heq, hd⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hd
    · exact diagAdj_symm hd
  · intro hd
    exact ⟨u, v, rfl, hd⟩

/-- Unique edge of `M` incident to cell `v` in a domicule tiling `hM`. -/
private noncomputable def edgeOf {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) (v : Board n) : Sym2 (Board n) :=
  (hM.2 v).choose

private theorem edgeOf_spec {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) (v : Board n) :
    edgeOf hM v ∈ M ∧ v ∈ edgeOf hM v :=
  (hM.2 v).choose_spec.1

private theorem edgeOf_unique {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) {v : Board n} {e : Sym2 (Board n)}
    (he : e ∈ M) (hv : v ∈ e) : e = edgeOf hM v :=
  (hM.2 v).choose_spec.2 e ⟨he, hv⟩

/-- Partner cell `mate hM v` matched to `v` by `M`. -/
private noncomputable def mate {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) (v : Board n) : Board n :=
  Sym2.Mem.other' (edgeOf_spec hM v).2

private theorem mk_mate_eq_edgeOf {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) (v : Board n) :
    s(v, mate hM v) = edgeOf hM v :=
  Sym2.other_spec' (edgeOf_spec hM v).2

private theorem mk_mate_mem {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) (v : Board n) :
    s(v, mate hM v) ∈ M := by
  rw [mk_mate_eq_edgeOf]
  exact (edgeOf_spec hM v).1

private theorem kingAdj_mate {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) (v : Board n) :
    kingAdj n v (mate hM v) :=
  (hM.1 (edgeOf hM v) (edgeOf_spec hM v).1).2 v (mate hM v) (mk_mate_eq_edgeOf hM v).symm

private theorem mk_mem_iff_mate {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) (u v : Board n) :
    s(u, v) ∈ M ↔ mate hM u = v := by
  constructor
  · intro he
    have heq : s(u, v) = s(u, mate hM u) := by
      rw [mk_mate_eq_edgeOf]
      exact edgeOf_unique hM he (Sym2.mem_mk_left u v)
    exact (Sym2.congr_right.mp heq).symm
  · rintro rfl
    exact mk_mate_mem hM u

private theorem mate_invol {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) (v : Board n) :
    mate hM (mate hM v) = v := by
  apply (mk_mem_iff_mate hM (mate hM v) v).mp
  rw [Sym2.eq_swap]
  exact mk_mate_mem hM v

private theorem mate_injective {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) : Function.Injective (mate hM) :=
  Function.Involutive.injective (mate_invol hM)

private theorem tiling_ext_mate {n : ℕ} {M₁ M₂ : Finset (Sym2 (Board n))}
    (hM₁ : IsDomiculeTiling n M₁) (hM₂ : IsDomiculeTiling n M₂)
    (h : ∀ v, mate hM₁ v = mate hM₂ v) : M₁ = M₂ := by
  ext e
  refine Sym2.ind (fun u v => ?_) e
  rw [mk_mem_iff_mate hM₁, mk_mem_iff_mate hM₂, h u]

/-- Build a domicule tiling from any king-adjacent involution `μ : Board n → Board n`. -/
private def matchingOfInvolution (n : ℕ) (μ : Board n → Board n) : Finset (Sym2 (Board n)) :=
  (Finset.univ : Finset (Board n)).image (fun v => s(v, μ v))

private theorem isDomiculeTiling_of_invol {n : ℕ} {μ : Board n → Board n}
    (hinv : ∀ v, μ (μ v) = v) (hadj : ∀ v, kingAdj n v (μ v)) :
    IsDomiculeTiling n (matchingOfInvolution n μ) := by
  constructor
  · intro e he
    rcases Finset.mem_image.mp he with ⟨v, _, rfl⟩
    exact edge_valid_mk (hadj v)
  · intro v
    refine ⟨s(v, μ v), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ v), Sym2.mem_mk_left v (μ v)⟩, ?_⟩
    rintro e ⟨he, hve⟩
    rcases Finset.mem_image.mp he with ⟨u, _, rfl⟩
    rcases Sym2.mem_iff.mp hve with rfl | rfl
    · rfl
    · rw [hinv u, Sym2.eq_swap]

private theorem mate_matchingOfInvolution {n : ℕ} {μ : Board n → Board n}
    (hinv : ∀ v, μ (μ v) = v) (hadj : ∀ v, kingAdj n v (μ v)) (v : Board n) :
    mate (isDomiculeTiling_of_invol hinv hadj) v = μ v :=
  (mk_mem_iff_mate (isDomiculeTiling_of_invol hinv hadj) v (μ v)).mp
    (Finset.mem_image_of_mem _ (Finset.mem_univ v))

/-! ### Section 2 (Steps 1 & 2): Four-Class `(r mod 2, c mod 2)` Partition & Edge Classification -/

/-- `n × n` block-index grid `I_n = Fin n × Fin n` (`|I_n| = n^2`). -/
private abbrev Idx (n : ℕ) : Type := Fin n × Fin n

private theorem card_idx (n : ℕ) : (Finset.univ : Finset (Idx n)).card = n ^ 2 := by
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  ring

private def embA (n : ℕ) (p : Idx n) : Board n :=
  (⟨2 * p.1.val, by omega⟩, ⟨2 * p.2.val, by omega⟩)

private def embB (n : ℕ) (p : Idx n) : Board n :=
  (⟨2 * p.1.val + 1, by omega⟩, ⟨2 * p.2.val + 1, by omega⟩)

private def embC (n : ℕ) (p : Idx n) : Board n :=
  (⟨2 * p.1.val, by omega⟩, ⟨2 * p.2.val + 1, by omega⟩)

private def embD (n : ℕ) (p : Idx n) : Board n :=
  (⟨2 * p.1.val + 1, by omega⟩, ⟨2 * p.2.val, by omega⟩)

private def blk (n : ℕ) (v : Board n) : Idx n :=
  (⟨v.1.val / 2, by omega⟩, ⟨v.2.val / 2, by omega⟩)

@[simp] private theorem blk_embA (n : ℕ) (p : Idx n) : blk n (embA n p) = p := by
  rcases p with ⟨i, j⟩
  exact Prod.ext (Fin.ext (by simp [blk, embA])) (Fin.ext (by simp [blk, embA]))

@[simp] private theorem blk_embB (n : ℕ) (p : Idx n) : blk n (embB n p) = p := by
  rcases p with ⟨i, j⟩
  exact Prod.ext (Fin.ext (by simp only [blk, embB]; omega))
    (Fin.ext (by simp only [blk, embB]; omega))

@[simp] private theorem blk_embC (n : ℕ) (p : Idx n) : blk n (embC n p) = p := by
  rcases p with ⟨i, j⟩
  exact Prod.ext (Fin.ext (by simp [blk, embC]))
    (Fin.ext (by simp only [blk, embC]; omega))

@[simp] private theorem blk_embD (n : ℕ) (p : Idx n) : blk n (embD n p) = p := by
  rcases p with ⟨i, j⟩
  exact Prod.ext (Fin.ext (by simp only [blk, embD]; omega))
    (Fin.ext (by simp [blk, embD]))

private theorem embA_injective (n : ℕ) : Function.Injective (embA n) :=
  Function.LeftInverse.injective (blk_embA n)

private theorem embB_injective (n : ℕ) : Function.Injective (embB n) :=
  Function.LeftInverse.injective (blk_embB n)

private theorem embC_injective (n : ℕ) : Function.Injective (embC n) :=
  Function.LeftInverse.injective (blk_embC n)

private theorem embD_injective (n : ℕ) : Function.Injective (embD n) :=
  Function.LeftInverse.injective (blk_embD n)

private theorem eq_embA_of_mod {n : ℕ} {v : Board n}
    (hr : v.1.val % 2 = 0) (hc : v.2.val % 2 = 0) : v = embA n (blk n v) := by
  rcases v with ⟨r, c⟩
  dsimp only at hr hc
  exact Prod.ext (Fin.ext (by simp only [embA, blk]; omega))
    (Fin.ext (by simp only [embA, blk]; omega))

private theorem eq_embB_of_mod {n : ℕ} {v : Board n}
    (hr : v.1.val % 2 = 1) (hc : v.2.val % 2 = 1) : v = embB n (blk n v) := by
  rcases v with ⟨r, c⟩
  dsimp only at hr hc
  exact Prod.ext (Fin.ext (by simp only [embB, blk]; omega))
    (Fin.ext (by simp only [embB, blk]; omega))

private theorem eq_embC_of_mod {n : ℕ} {v : Board n}
    (hr : v.1.val % 2 = 0) (hc : v.2.val % 2 = 1) : v = embC n (blk n v) := by
  rcases v with ⟨r, c⟩
  dsimp only at hr hc
  exact Prod.ext (Fin.ext (by simp only [embC, blk]; omega))
    (Fin.ext (by simp only [embC, blk]; omega))

private theorem eq_embD_of_mod {n : ℕ} {v : Board n}
    (hr : v.1.val % 2 = 1) (hc : v.2.val % 2 = 0) : v = embD n (blk n v) := by
  rcases v with ⟨r, c⟩
  dsimp only at hr hc
  exact Prod.ext (Fin.ext (by simp only [embD, blk]; omega))
    (Fin.ext (by simp only [embD, blk]; omega))

/-- Step 1 four-class partition of `Board n`. -/
private theorem board_four_cases {n : ℕ} (v : Board n) :
    v = embA n (blk n v) ∨ v = embB n (blk n v) ∨
      v = embC n (blk n v) ∨ v = embD n (blk n v) := by
  rcases Nat.mod_two_eq_zero_or_one v.1.val with hr0 | hr1 <;>
    rcases Nat.mod_two_eq_zero_or_one v.2.val with hc0 | hc1
  · exact Or.inl (eq_embA_of_mod hr0 hc0)
  · exact Or.inr (Or.inr (Or.inl (eq_embC_of_mod hr0 hc1)))
  · exact Or.inr (Or.inr (Or.inr (eq_embD_of_mod hr1 hc0)))
  · exact Or.inr (Or.inl (eq_embB_of_mod hr1 hc1))

/-- Step 2: Diagonal neighbors flip both `r mod 2` and `c mod 2` (`A ↔ B`, `C ↔ D`). -/
private theorem diagAdj_embA_target {n : ℕ} {p : Idx n} {v : Board n}
    (h : diagAdj n (embA n p) v) : v = embB n (blk n v) := by
  rcases h with ⟨h1, h2⟩
  simp only [embA, nat_dist_def] at h1 h2
  exact eq_embB_of_mod (by omega) (by omega)

private theorem diagAdj_embB_target {n : ℕ} {p : Idx n} {v : Board n}
    (h : diagAdj n (embB n p) v) : v = embA n (blk n v) := by
  rcases h with ⟨h1, h2⟩
  simp only [embB, nat_dist_def] at h1 h2
  exact eq_embA_of_mod (by omega) (by omega)

private theorem diagAdj_embC_target {n : ℕ} {p : Idx n} {v : Board n}
    (h : diagAdj n (embC n p) v) : v = embD n (blk n v) := by
  rcases h with ⟨h1, h2⟩
  simp only [embC, nat_dist_def] at h1 h2
  exact eq_embD_of_mod (by omega) (by omega)

private theorem diagAdj_embD_target {n : ℕ} {p : Idx n} {v : Board n}
    (h : diagAdj n (embD n p) v) : v = embC n (blk n v) := by
  rcases h with ⟨h1, h2⟩
  simp only [embD, nat_dist_def] at h1 h2
  exact eq_embC_of_mod (by omega) (by omega)

/-- Step 2 (`A`–`B` diagonal coordinate inequalities): `q.1 ≤ p.1 ≤ q.1 + 1` and `q.2 ≤ p.2 ≤ q.2 + 1`. -/
private theorem diagAdj_embA_embB_iff {n : ℕ} (p q : Idx n) :
    diagAdj n (embA n p) (embB n q) ↔
      q.1.val ≤ p.1.val ∧ p.1.val ≤ q.1.val + 1 ∧
        q.2.val ≤ p.2.val ∧ p.2.val ≤ q.2.val + 1 := by
  simp only [diagAdj, embA, embB, nat_dist_def]
  omega

/-- Step 2 (`C`–`D` diagonal coordinate inequalities): note the OPPOSITE column inequality
`p.2 ≤ q.2 ≤ p.2 + 1`! -/
private theorem diagAdj_embC_embD_iff {n : ℕ} (p q : Idx n) :
    diagAdj n (embC n p) (embD n q) ↔
      q.1.val ≤ p.1.val ∧ p.1.val ≤ q.1.val + 1 ∧
        p.2.val ≤ q.2.val ∧ q.2.val ≤ p.2.val + 1 := by
  simp only [diagAdj, embC, embD, nat_dist_def]
  omega

/-- Orthogonal edges flip `(r + c) mod 2` (`V_0 ↔ V_1`). -/
private theorem orth_parity_flip {n : ℕ} {u v : Board n}
    (hk : kingAdj n u v) (hnd : ¬ diagAdj n u v) :
    (u.1.val + u.2.val) % 2 = 1 - (v.1.val + v.2.val) % 2 := by
  rcases hk with ⟨hne, h1, h2⟩
  have hne_val : u.1.val ≠ v.1.val ∨ u.2.val ≠ v.2.val := by
    by_contra hall
    apply hne
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  simp only [diagAdj, nat_dist_def] at h1 h2 hnd
  omega

/-- Step 2 (`H_even`, `A`–`C`): horizontal domino in row `2 * p.1` with `q.1 = p.1` and `q.2 ≤ p.2 ≤ q.2 + 1`. -/
private theorem kingAdj_embA_embC_iff {n : ℕ} (p q : Idx n) :
    kingAdj n (embA n p) (embC n q) ↔
      q.1 = p.1 ∧ q.2.val ≤ p.2.val ∧ p.2.val ≤ q.2.val + 1 := by
  constructor
  · rintro ⟨_, h1, h2⟩
    simp only [embA, embC, nat_dist_def] at h1 h2
    refine ⟨Fin.ext (by omega), by omega, by omega⟩
  · rintro ⟨hq1, hlo, hhi⟩
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      have hc := congrArg (fun x : Board n => x.2.val) heq
      simp only [embA, embC] at hc
      omega
    · simp only [embA, embC, nat_dist_def, hq1]
      omega
    · simp only [embA, embC, nat_dist_def]
      omega

/-- Step 2 (`H_odd`, `B`–`D`): horizontal domino in row `2 * p.1 + 1` with `q.1 = p.1` and `p.2 ≤ q.2 ≤ p.2 + 1`. -/
private theorem kingAdj_embB_embD_iff {n : ℕ} (p q : Idx n) :
    kingAdj n (embB n p) (embD n q) ↔
      q.1 = p.1 ∧ p.2.val ≤ q.2.val ∧ q.2.val ≤ p.2.val + 1 := by
  constructor
  · rintro ⟨_, h1, h2⟩
    simp only [embB, embD, nat_dist_def] at h1 h2
    refine ⟨Fin.ext (by omega), by omega, by omega⟩
  · rintro ⟨hq1, hlo, hhi⟩
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      have hc := congrArg (fun x : Board n => x.2.val) heq
      simp only [embB, embD] at hc
      omega
    · simp only [embB, embD, nat_dist_def, hq1]
      omega
    · simp only [embB, embD, nat_dist_def]
      omega

/-! ### Section 3 (Step 3): Parity of Diagonal Domicules (`d_0 = d_1` and `|M_diag| = 2 * d_0`) -/

section Parity

open scoped Classical

private noncomputable def diagIdxA {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    Finset (Idx n) :=
  Finset.univ.filter (fun p => diagAdj n (embA n p) (mate hM (embA n p)))

private noncomputable def diagIdxB {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    Finset (Idx n) :=
  Finset.univ.filter (fun p => diagAdj n (embB n p) (mate hM (embB n p)))

private noncomputable def diagIdxC {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    Finset (Idx n) :=
  Finset.univ.filter (fun p => diagAdj n (embC n p) (mate hM (embC n p)))

private noncomputable def diagIdxD {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    Finset (Idx n) :=
  Finset.univ.filter (fun p => diagAdj n (embD n p) (mate hM (embD n p)))

private noncomputable def orthIdxA {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    Finset (Idx n) :=
  Finset.univ.filter (fun p => ¬ diagAdj n (embA n p) (mate hM (embA n p)))

private noncomputable def orthIdxB {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    Finset (Idx n) :=
  Finset.univ.filter (fun p => ¬ diagAdj n (embB n p) (mate hM (embB n p)))

private noncomputable def orthIdxC {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    Finset (Idx n) :=
  Finset.univ.filter (fun p => ¬ diagAdj n (embC n p) (mate hM (embC n p)))

private noncomputable def orthIdxD {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    Finset (Idx n) :=
  Finset.univ.filter (fun p => ¬ diagAdj n (embD n p) (mate hM (embD n p)))

private theorem card_diagIdxB_eq {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    (diagIdxB hM).card = (diagIdxA hM).card := by
  symm
  refine Finset.card_bij (fun p _ => blk n (mate hM (embA n p))) ?_ ?_ ?_
  · intro p hp
    simp only [diagIdxA, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [diagIdxB, Finset.mem_filter, Finset.mem_univ, true_and]
    have htarget : mate hM (embA n p) = embB n (blk n (mate hM (embA n p))) :=
      diagAdj_embA_target hp
    rw [← htarget, mate_invol hM]
    exact diagAdj_symm hp
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [diagIdxA, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    have ht₁ := diagAdj_embA_target hp₁
    have ht₂ := diagAdj_embA_target hp₂
    have hm : mate hM (embA n p₁) = mate hM (embA n p₂) := by rw [ht₁, ht₂, heq]
    exact embA_injective n (mate_injective hM hm)
  · intro q hq
    simp only [diagIdxB, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have htarget : mate hM (embB n q) = embA n (blk n (mate hM (embB n q))) :=
      diagAdj_embB_target hq
    refine ⟨blk n (mate hM (embB n q)), ?_, ?_⟩
    · simp only [diagIdxA, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← htarget, mate_invol hM]
      exact diagAdj_symm hq
    · rw [← htarget, mate_invol hM, blk_embB]

private theorem card_diagIdxD_eq {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    (diagIdxD hM).card = (diagIdxC hM).card := by
  symm
  refine Finset.card_bij (fun p _ => blk n (mate hM (embC n p))) ?_ ?_ ?_
  · intro p hp
    simp only [diagIdxC, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [diagIdxD, Finset.mem_filter, Finset.mem_univ, true_and]
    have htarget : mate hM (embC n p) = embD n (blk n (mate hM (embC n p))) :=
      diagAdj_embC_target hp
    rw [← htarget, mate_invol hM]
    exact diagAdj_symm hp
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [diagIdxC, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    have ht₁ := diagAdj_embC_target hp₁
    have ht₂ := diagAdj_embC_target hp₂
    have hm : mate hM (embC n p₁) = mate hM (embC n p₂) := by rw [ht₁, ht₂, heq]
    exact embC_injective n (mate_injective hM hm)
  · intro q hq
    simp only [diagIdxD, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have htarget : mate hM (embD n q) = embC n (blk n (mate hM (embD n q))) :=
      diagAdj_embD_target hq
    refine ⟨blk n (mate hM (embD n q)), ?_, ?_⟩
    · simp only [diagIdxC, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← htarget, mate_invol hM]
      exact diagAdj_symm hq
    · rw [← htarget, mate_invol hM, blk_embD]

private theorem card_diag_add_orth_A {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    (diagIdxA hM).card + (orthIdxA hM).card = n ^ 2 := by
  unfold diagIdxA orthIdxA
  rw [Finset.card_filter_add_card_filter_not, card_idx]

private theorem card_diag_add_orth_B {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    (diagIdxB hM).card + (orthIdxB hM).card = n ^ 2 := by
  unfold diagIdxB orthIdxB
  rw [Finset.card_filter_add_card_filter_not, card_idx]

private theorem card_diag_add_orth_C {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    (diagIdxC hM).card + (orthIdxC hM).card = n ^ 2 := by
  unfold diagIdxC orthIdxC
  rw [Finset.card_filter_add_card_filter_not, card_idx]

private theorem card_diag_add_orth_D {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    (diagIdxD hM).card + (orthIdxD hM).card = n ^ 2 := by
  unfold diagIdxD orthIdxD
  rw [Finset.card_filter_add_card_filter_not, card_idx]

private theorem card_orthV0_eq_orthV1 {n : ℕ} {M : Finset (Sym2 (Board n))} (hM : IsDomiculeTiling n M) :
    ((Finset.univ : Finset (Board n)).filter
      (fun v => (v.1.val + v.2.val) % 2 = 0 ∧ ¬ diagAdj n v (mate hM v))).card =
    ((Finset.univ : Finset (Board n)).filter
      (fun v => (v.1.val + v.2.val) % 2 = 1 ∧ ¬ diagAdj n v (mate hM v))).card := by
  refine Finset.card_bij (fun v _ => mate hM v) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    have hflip := orth_parity_flip (kingAdj_mate hM v) hv.2
    refine ⟨by omega, ?_⟩
    rw [mate_invol hM]
    exact fun hd => hv.2 (diagAdj_symm hd)
  · intro v₁ _ v₂ _ heq
    exact mate_injective hM heq
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨mate hM w, ?_, mate_invol hM w⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hflip := orth_parity_flip (kingAdj_mate hM w) hw.2
    refine ⟨by omega, ?_⟩
    rw [mate_invol hM]
    exact fun hd => hw.2 (diagAdj_symm hd)

private theorem card_orthIdxA_eq_orthIdxC {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) :
    (orthIdxA hM).card = (orthIdxC hM).card := by
  let orthV0 := (Finset.univ : Finset (Board n)).filter
    (fun v => (v.1.val + v.2.val) % 2 = 0 ∧ ¬ diagAdj n v (mate hM v))
  let orthV1 := (Finset.univ : Finset (Board n)).filter
    (fun v => (v.1.val + v.2.val) % 2 = 1 ∧ ¬ diagAdj n v (mate hM v))
  have h0 : orthV0 = (orthIdxA hM).image (embA n) ∪ (orthIdxB hM).image (embB n) := by
    ext v
    simp only [orthV0, orthIdxA, orthIdxB, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hpar, hnd⟩
      rcases board_four_cases v with hv | hv | hv | hv
      · left; exact ⟨blk n v, by rwa [← hv], hv.symm⟩
      · right; exact ⟨blk n v, by rwa [← hv], hv.symm⟩
      · exfalso; rw [hv] at hpar; simp only [embC] at hpar; omega
      · exfalso; rw [hv] at hpar; simp only [embD] at hpar; omega
    · rintro (⟨p, hnd, rfl⟩ | ⟨p, hnd, rfl⟩)
      · exact ⟨by simp only [embA]; omega, hnd⟩
      · exact ⟨by simp only [embB]; omega, hnd⟩
  have h1 : orthV1 = (orthIdxC hM).image (embC n) ∪ (orthIdxD hM).image (embD n) := by
    ext v
    simp only [orthV1, orthIdxC, orthIdxD, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hpar, hnd⟩
      rcases board_four_cases v with hv | hv | hv | hv
      · exfalso; rw [hv] at hpar; simp only [embA] at hpar; omega
      · exfalso; rw [hv] at hpar; simp only [embB] at hpar; omega
      · left; exact ⟨blk n v, by rwa [← hv], hv.symm⟩
      · right; exact ⟨blk n v, by rwa [← hv], hv.symm⟩
    · rintro (⟨p, hnd, rfl⟩ | ⟨p, hnd, rfl⟩)
      · exact ⟨by simp only [embC]; omega, hnd⟩
      · exact ⟨by simp only [embD]; omega, hnd⟩
  have hdisj0 : Disjoint ((orthIdxA hM).image (embA n)) ((orthIdxB hM).image (embB n)) := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    rcases Finset.mem_image.mp hvA with ⟨p, _, rfl⟩
    rcases Finset.mem_image.mp hvB with ⟨q, _, heq⟩
    have hr := congrArg (fun x : Board n => x.1.val) heq
    simp only [embA, embB] at hr
    omega
  have hdisj1 : Disjoint ((orthIdxC hM).image (embC n)) ((orthIdxD hM).image (embD n)) := by
    rw [Finset.disjoint_left]
    intro v hvC hvD
    rcases Finset.mem_image.mp hvC with ⟨p, _, rfl⟩
    rcases Finset.mem_image.mp hvD with ⟨q, _, heq⟩
    have hr := congrArg (fun x : Board n => x.1.val) heq
    simp only [embC, embD] at hr
    omega
  have hc0 : orthV0.card = (orthIdxA hM).card + (orthIdxB hM).card := by
    rw [h0, Finset.card_union_of_disjoint hdisj0,
      Finset.card_image_of_injective _ (embA_injective n),
      Finset.card_image_of_injective _ (embB_injective n)]
  have hc1 : orthV1.card = (orthIdxC hM).card + (orthIdxD hM).card := by
    rw [h1, Finset.card_union_of_disjoint hdisj1,
      Finset.card_image_of_injective _ (embC_injective n),
      Finset.card_image_of_injective _ (embD_injective n)]
  have heq01 : orthV0.card = orthV1.card := card_orthV0_eq_orthV1 hM
  have hbA := card_diag_add_orth_A hM
  have hbB := card_diag_add_orth_B hM
  have hbC := card_diag_add_orth_C hM
  have hbD := card_diag_add_orth_D hM
  have hdAB := card_diagIdxB_eq hM
  have hdCD := card_diagIdxD_eq hM
  omega

private theorem card_diagIdxA_eq_diagIdxC {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) :
    (diagIdxA hM).card = (diagIdxC hM).card := by
  have h1 := card_diag_add_orth_A hM
  have h2 := card_diag_add_orth_C hM
  have h3 := card_orthIdxA_eq_orthIdxC hM
  omega

/-- Step 3 (`SCOPING-S017.md` §2.1): `(M.filter (IsDiagDomicule n)).card = 2 * (diagIdxA hM).card`. -/
private theorem filter_diag_card_eq_two_mul {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) :
    (M.filter (IsDiagDomicule n)).card = 2 * (diagIdxA hM).card := by
  let edgesA := (diagIdxA hM).image (fun p => s(embA n p, mate hM (embA n p)))
  let edgesC := (diagIdxC hM).image (fun p => s(embC n p, mate hM (embC n p)))
  have hpart : M.filter (IsDiagDomicule n) = edgesA ∪ edgesC := by
    ext e
    refine Sym2.ind (fun u v => ?_) e
    simp only [Finset.mem_filter, isDiagDomicule_mk, edgesA, edgesC, Finset.mem_union,
      Finset.mem_image, diagIdxA, diagIdxC, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨heM, hdiag⟩
      have hmu : mate hM u = v := (mk_mem_iff_mate hM u v).mp heM
      have hmv : mate hM v = u := by rw [← hmu, mate_invol hM]
      rcases board_four_cases u with hu | hu | hu | hu
      · left
        refine ⟨blk n u, ?_, ?_⟩
        · rwa [← hu, hmu]
        · rw [← hu, hmu]
      · left
        have hvA : v = embA n (blk n v) := diagAdj_embB_target (hu ▸ hdiag)
        refine ⟨blk n v, ?_, ?_⟩
        · rw [← hvA, hmv]
          exact diagAdj_symm hdiag
        · rw [← hvA, hmv, Sym2.eq_swap]
      · right
        refine ⟨blk n u, ?_, ?_⟩
        · rwa [← hu, hmu]
        · rw [← hu, hmu]
      · right
        have hvC : v = embC n (blk n v) := diagAdj_embD_target (hu ▸ hdiag)
        refine ⟨blk n v, ?_, ?_⟩
        · rw [← hvC, hmv]
          exact diagAdj_symm hdiag
        · rw [← hvC, hmv, Sym2.eq_swap]
    · rintro (⟨p, hdiag, heq⟩ | ⟨p, hdiag, heq⟩)
      · have heM : s(u, v) ∈ M := heq ▸ mk_mate_mem hM (embA n p)
        have hduv : diagAdj n u v :=
          (isDiagDomicule_mk u v).mp (heq ▸ (isDiagDomicule_mk _ _).mpr hdiag)
        exact ⟨heM, hduv⟩
      · have heM : s(u, v) ∈ M := heq ▸ mk_mate_mem hM (embC n p)
        have hduv : diagAdj n u v :=
          (isDiagDomicule_mk u v).mp (heq ▸ (isDiagDomicule_mk _ _).mpr hdiag)
        exact ⟨heM, hduv⟩
  have hdisj : Disjoint edgesA edgesC := by
    rw [Finset.disjoint_left]
    intro e heA heC
    rcases Finset.mem_image.mp heA with ⟨p, _, rfl⟩
    rcases Finset.mem_image.mp heC with ⟨q, hq, heq⟩
    simp only [diagIdxC, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have htarget : mate hM (embC n q) = embD n (blk n (mate hM (embC n q))) :=
      diagAdj_embC_target hq
    rw [htarget] at heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨_, h2⟩
    · have hc := congrArg (fun x : Board n => x.2.val) h1
      simp only [embA, embC] at hc
      omega
    · have hr := congrArg (fun x : Board n => x.1.val) h2
      simp only [embA, embD] at hr
      omega
  have hinjA : Set.InjOn (fun p => s(embA n p, mate hM (embA n p))) (diagIdxA hM) := by
    intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_coe, diagIdxA, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    have ht₂ := diagAdj_embA_target hp₂
    rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact embA_injective n h1
    · exfalso
      rw [ht₂] at h1
      have hr := congrArg (fun x : Board n => x.1.val) h1
      simp only [embA, embB] at hr
      omega
  have hinjC : Set.InjOn (fun p => s(embC n p, mate hM (embC n p))) (diagIdxC hM) := by
    intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_coe, diagIdxC, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    have ht₂ := diagAdj_embC_target hp₂
    rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact embC_injective n h1
    · exfalso
      rw [ht₂] at h1
      have hr := congrArg (fun x : Board n => x.1.val) h1
      simp only [embC, embD] at hr
      omega
  rw [hpart, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn hinjA, Finset.card_image_of_injOn hinjC,
    card_diagIdxA_eq_diagIdxC hM, two_mul]

end Parity

/-! ### Section 4: Nonnegative Coordinate-Sum Vanishing & Finite Pigeonhole Helpers -/

private theorem image_eq_of_injOn_of_card_eq {α β : Type*} [DecidableEq β]
    {S : Finset α} {T : Finset β} {φ : α → β}
    (hmaps : ∀ x ∈ S, φ x ∈ T) (hinj : Set.InjOn φ S) (hcard : T.card ≤ S.card) :
    S.image φ = T := by
  have hsurj :=
    Finset.surj_on_of_inj_on_of_card_le (fun x _ => φ x) hmaps
      (fun x₁ x₂ hx₁ hx₂ h => hinj hx₁ hx₂ h) hcard
  ext y
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hmaps x hx
  · intro hy
    rcases hsurj y hy with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- Finite pigeonhole + `Finset.sum_eq_zero_iff_of_nonneg` for an injective self-map with `w (φ x) ≤ w x`. -/
private theorem injOn_endo_eq_of_le {α : Type*} [DecidableEq α]
    {S : Finset α} {φ : α → α} (w : α → ℕ)
    (hmaps : ∀ x ∈ S, φ x ∈ S) (hinj : Set.InjOn φ S) (hle : ∀ x ∈ S, w (φ x) ≤ w x) :
    ∀ x ∈ S, w (φ x) = w x := by
  have himg : S.image φ = S := image_eq_of_injOn_of_card_eq hmaps hinj le_rfl
  have hadd : (∑ x ∈ S, (w x - w (φ x))) + ∑ x ∈ S, w (φ x) = ∑ x ∈ S, w x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have := hle x hx
    omega
  have himg_sum : ∑ x ∈ S, w (φ x) = ∑ y ∈ S, w y := by
    rw [← Finset.sum_image hinj, himg]
  rw [himg_sum] at hadd
  have hzero : ∑ x ∈ S, (w x - w (φ x)) = 0 := by omega
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hzero
  intro x hx
  have h0 := hall x hx
  have h1 := hle x hx
  omega

/-- Dual version of `injOn_endo_eq_of_le` when `w x ≤ w (φ x)` on `S`. -/
private theorem injOn_endo_eq_of_ge {α : Type*} [DecidableEq α]
    {S : Finset α} {φ : α → α} (w : α → ℕ)
    (hmaps : ∀ x ∈ S, φ x ∈ S) (hinj : Set.InjOn φ S) (hge : ∀ x ∈ S, w x ≤ w (φ x)) :
    ∀ x ∈ S, w (φ x) = w x := by
  have himg : S.image φ = S := image_eq_of_injOn_of_card_eq hmaps hinj le_rfl
  have hadd : (∑ x ∈ S, (w (φ x) - w x)) + ∑ x ∈ S, w x = ∑ x ∈ S, w (φ x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have := hge x hx
    omega
  have himg_sum : ∑ x ∈ S, w (φ x) = ∑ y ∈ S, w y := by
    rw [← Finset.sum_image hinj, himg]
  rw [himg_sum] at hadd
  have hzero : ∑ x ∈ S, (w (φ x) - w x) = 0 := by omega
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hzero
  intro x hx
  have h0 := hall x hx
  have h1 := hge x hx
  omega

/-- Punctured coordinate-sum identity on `Finset.univ.erase a₀ → Finset.univ.erase b₀` (`w (φ x) ≤ w x`). -/
private theorem punctured_bij_sum_diff {α : Type*} [Fintype α] [DecidableEq α]
    {a₀ b₀ : α} {φ : α → α} (w : α → ℕ)
    (hmaps : ∀ x ∈ (Finset.univ : Finset α).erase a₀, φ x ∈ (Finset.univ : Finset α).erase b₀)
    (hinj : Set.InjOn φ ((Finset.univ : Finset α).erase a₀))
    (hle : ∀ x ∈ (Finset.univ : Finset α).erase a₀, w (φ x) ≤ w x) :
    (∑ x ∈ (Finset.univ : Finset α).erase a₀, (w x - w (φ x))) + w a₀ = w b₀ := by
  set S := (Finset.univ : Finset α).erase a₀
  set T := (Finset.univ : Finset α).erase b₀
  have hcard : T.card ≤ S.card := by
    simp [S, T, Finset.card_erase_of_mem]
  have himg : S.image φ = T := image_eq_of_injOn_of_card_eq hmaps hinj hcard
  have hadd : (∑ x ∈ S, (w x - w (φ x))) + ∑ x ∈ S, w (φ x) = ∑ x ∈ S, w x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have := hle x hx
    omega
  have himg_sum : ∑ x ∈ S, w (φ x) = ∑ y ∈ T, w y := by
    rw [← Finset.sum_image hinj, himg]
  rw [himg_sum] at hadd
  have hS : (∑ x ∈ S, w x) + w a₀ = ∑ x ∈ (Finset.univ : Finset α), w x :=
    Finset.sum_erase_add Finset.univ w (Finset.mem_univ a₀)
  have hT : (∑ y ∈ T, w y) + w b₀ = ∑ y ∈ (Finset.univ : Finset α), w y :=
    Finset.sum_erase_add Finset.univ w (Finset.mem_univ b₀)
  omega

/-- Dual punctured coordinate-sum identity (`w x ≤ w (ψ x)`). -/
private theorem punctured_bij_sum_diff_ge {α : Type*} [Fintype α] [DecidableEq α]
    {c₀ d₀ : α} {ψ : α → α} (w : α → ℕ)
    (hmaps : ∀ x ∈ (Finset.univ : Finset α).erase c₀, ψ x ∈ (Finset.univ : Finset α).erase d₀)
    (hinj : Set.InjOn ψ ((Finset.univ : Finset α).erase c₀))
    (hge : ∀ x ∈ (Finset.univ : Finset α).erase c₀, w x ≤ w (ψ x)) :
    (∑ x ∈ (Finset.univ : Finset α).erase c₀, (w (ψ x) - w x)) + w d₀ = w c₀ := by
  set S := (Finset.univ : Finset α).erase c₀
  set T := (Finset.univ : Finset α).erase d₀
  have hcard : T.card ≤ S.card := by
    simp [S, T, Finset.card_erase_of_mem]
  have himg : S.image ψ = T := image_eq_of_injOn_of_card_eq hmaps hinj hcard
  have hadd : (∑ x ∈ S, (w (ψ x) - w x)) + ∑ x ∈ S, w x = ∑ x ∈ S, w (ψ x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have := hge x hx
    omega
  have himg_sum : ∑ x ∈ S, w (ψ x) = ∑ y ∈ T, w y := by
    rw [← Finset.sum_image hinj, himg]
  rw [himg_sum] at hadd
  have hS : (∑ x ∈ S, w x) + w c₀ = ∑ x ∈ (Finset.univ : Finset α), w x :=
    Finset.sum_erase_add Finset.univ w (Finset.mem_univ c₀)
  have hT : (∑ y ∈ T, w y) + w d₀ = ∑ y ∈ (Finset.univ : Finset α), w y :=
    Finset.sum_erase_add Finset.univ w (Finset.mem_univ d₀)
  omega

/-! ### Section 5 (Step 4): Proof of Identity 1 (`domiculeTilings_max_diag_eq_one`) -/

/-- Flip parity within each `2`-cell pair `{2i, 2i + 1}` on `Fin (2 * n)`. -/
private def flip2 (n : ℕ) (x : Fin (2 * n)) : Fin (2 * n) :=
  if h : x.val % 2 = 0 then ⟨x.val + 1, by omega⟩ else ⟨x.val - 1, by omega⟩

private theorem flip2_val_of_even {n : ℕ} {x : Fin (2 * n)} (h : x.val % 2 = 0) :
    (flip2 n x).val = x.val + 1 := by
  simp [flip2, h]

private theorem flip2_val_of_odd {n : ℕ} {x : Fin (2 * n)} (h : x.val % 2 ≠ 0) :
    (flip2 n x).val = x.val - 1 := by
  simp [flip2, h]

private theorem flip2_div (n : ℕ) (x : Fin (2 * n)) : (flip2 n x).val / 2 = x.val / 2 := by
  by_cases h : x.val % 2 = 0
  · rw [flip2_val_of_even h]; omega
  · rw [flip2_val_of_odd h]; omega

private theorem flip2_invol (n : ℕ) (x : Fin (2 * n)) : flip2 n (flip2 n x) = x := by
  by_cases h : x.val % 2 = 0
  · have h1 := flip2_val_of_even h
    have ho : (flip2 n x).val % 2 ≠ 0 := by omega
    have h2 := flip2_val_of_odd ho
    exact Fin.ext (by omega)
  · have h1 := flip2_val_of_odd h
    have he : (flip2 n x).val % 2 = 0 := by omega
    have h2 := flip2_val_of_even he
    exact Fin.ext (by omega)

private theorem flip2_dist (n : ℕ) (x : Fin (2 * n)) : Nat.dist x.val (flip2 n x).val = 1 := by
  by_cases h : x.val % 2 = 0
  · rw [flip2_val_of_even h, nat_dist_def]; omega
  · rw [flip2_val_of_odd h, nat_dist_def]; omega

/-- Involution of the canonical all-diagonal `2 × 2` X-cross matching `M_*`. -/
private def muStar (n : ℕ) (v : Board n) : Board n :=
  (flip2 n v.1, flip2 n v.2)

private theorem muStar_invol (n : ℕ) (v : Board n) : muStar n (muStar n v) = v := by
  rcases v with ⟨r, c⟩
  simp [muStar, flip2_invol]

private theorem muStar_diagAdj (n : ℕ) (v : Board n) : diagAdj n v (muStar n v) :=
  ⟨flip2_dist n v.1, flip2_dist n v.2⟩

private theorem muStar_kingAdj (n : ℕ) (v : Board n) : kingAdj n v (muStar n v) :=
  diagAdj_imp_kingAdj (muStar_diagAdj n v)

@[simp] private theorem muStar_embA (n : ℕ) (p : Idx n) : muStar n (embA n p) = embB n p := by
  rcases p with ⟨i, j⟩
  exact Prod.ext (Fin.ext (by simp [muStar, embA, embB, flip2]))
    (Fin.ext (by simp [muStar, embA, embB, flip2]))

@[simp] private theorem muStar_embB (n : ℕ) (p : Idx n) : muStar n (embB n p) = embA n p := by
  rw [← muStar_embA, muStar_invol]

@[simp] private theorem muStar_embC (n : ℕ) (p : Idx n) : muStar n (embC n p) = embD n p := by
  rcases p with ⟨i, j⟩
  refine Prod.ext (Fin.ext (by simp [muStar, embC, embD, flip2])) (Fin.ext ?_)
  change (flip2 n (embC n (i, j)).2).val = 2 * j.val
  have ho : (embC n (i, j)).2.val % 2 ≠ 0 := by simp only [embC]; omega
  rw [flip2_val_of_odd ho]
  simp [embC]

@[simp] private theorem muStar_embD (n : ℕ) (p : Idx n) : muStar n (embD n p) = embC n p := by
  rw [← muStar_embC, muStar_invol]

/-- Canonical all-diagonal `2 × 2` X-cross domicule tiling `M_*`. -/
private def M_star (n : ℕ) : Finset (Sym2 (Board n)) :=
  matchingOfInvolution n (muStar n)

private theorem isDomiculeTiling_M_star (n : ℕ) : IsDomiculeTiling n (M_star n) :=
  isDomiculeTiling_of_invol (muStar_invol n) (muStar_kingAdj n)

private theorem mate_M_star (n : ℕ) (v : Board n) :
    mate (isDomiculeTiling_M_star n) v = muStar n v :=
  mate_matchingOfInvolution (muStar_invol n) (muStar_kingAdj n) v

open scoped Classical in
private theorem card_diag_M_star (n : ℕ) :
    ((M_star n).filter (IsDiagDomicule n)).card = 2 * (n ^ 2) := by
  have hM := isDomiculeTiling_M_star n
  rw [filter_diag_card_eq_two_mul hM]
  have hfull : diagIdxA hM = Finset.univ := by
    ext p
    simp only [diagIdxA, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, mate_M_star]
    exact muStar_diagAdj n (embA n p)
  rw [hfull, card_idx]

open scoped Classical in
/-- Step 4 uniqueness: any domicule tiling with `2 * n^2` diagonal domicules equals `M_star n`. -/
private theorem eq_M_star_of_max_diag {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) (hcard : (M.filter (IsDiagDomicule n)).card = 2 * (n ^ 2)) :
    M = M_star n := by
  have hdA : (diagIdxA hM).card = n ^ 2 := by
    have := filter_diag_card_eq_two_mul hM
    omega
  have hdC : (diagIdxC hM).card = n ^ 2 := by
    rw [← card_diagIdxA_eq_diagIdxC hM]
    exact hdA
  have horthA0 : (orthIdxA hM).card = 0 := by
    have := card_diag_add_orth_A hM
    omega
  have horthC0 : (orthIdxC hM).card = 0 := by
    have := card_diag_add_orth_C hM
    omega
  have hallA : ∀ p : Idx n, diagAdj n (embA n p) (mate hM (embA n p)) := by
    intro p
    by_contra hnd
    have hp : p ∈ orthIdxA hM := by simp [orthIdxA, hnd]
    have hpos : 0 < (orthIdxA hM).card := Finset.card_pos.mpr ⟨p, hp⟩
    omega
  have hallC : ∀ p : Idx n, diagAdj n (embC n p) (mate hM (embC n p)) := by
    intro p
    by_contra hnd
    have hp : p ∈ orthIdxC hM := by simp [orthIdxC, hnd]
    have hpos : 0 < (orthIdxC hM).card := Finset.card_pos.mpr ⟨p, hp⟩
    omega
  let φ : Idx n → Idx n := fun p => blk n (mate hM (embA n p))
  let ψ : Idx n → Idx n := fun p => blk n (mate hM (embC n p))
  have hφ_eq : ∀ p, mate hM (embA n p) = embB n (φ p) := fun p => diagAdj_embA_target (hallA p)
  have hψ_eq : ∀ p, mate hM (embC n p) = embD n (ψ p) := fun p => diagAdj_embC_target (hallC p)
  have hφ_inj : Set.InjOn φ (Finset.univ : Finset (Idx n)) := by
    intro p₁ _ p₂ _ heq
    have hm : mate hM (embA n p₁) = mate hM (embA n p₂) := by rw [hφ_eq, hφ_eq, heq]
    exact embA_injective n (mate_injective hM hm)
  have hψ_inj : Set.InjOn ψ (Finset.univ : Finset (Idx n)) := by
    intro p₁ _ p₂ _ heq
    have hm : mate hM (embC n p₁) = mate hM (embC n p₂) := by rw [hψ_eq, hψ_eq, heq]
    exact embC_injective n (mate_injective hM hm)
  have hφ_step : ∀ p : Idx n, (φ p).1.val ≤ p.1.val ∧ (φ p).2.val ≤ p.2.val := by
    intro p
    have hd := hallA p
    rw [hφ_eq p, diagAdj_embA_embB_iff] at hd
    exact ⟨hd.1, hd.2.2.1⟩
  have hψ_step : ∀ p : Idx n, (ψ p).1.val ≤ p.1.val ∧ p.2.val ≤ (ψ p).2.val := by
    intro p
    have hd := hallC p
    rw [hψ_eq p, diagAdj_embC_embD_iff] at hd
    exact ⟨hd.1, hd.2.2.1⟩
  have hφ1 := injOn_endo_eq_of_le (fun p : Idx n => p.1.val)
    (fun _ _ => Finset.mem_univ _) hφ_inj (fun p _ => (hφ_step p).1)
  have hφ2 := injOn_endo_eq_of_le (fun p : Idx n => p.2.val)
    (fun _ _ => Finset.mem_univ _) hφ_inj (fun p _ => (hφ_step p).2)
  have hψ1 := injOn_endo_eq_of_le (fun p : Idx n => p.1.val)
    (fun _ _ => Finset.mem_univ _) hψ_inj (fun p _ => (hψ_step p).1)
  have hψ2 := injOn_endo_eq_of_ge (fun p : Idx n => p.2.val)
    (fun _ _ => Finset.mem_univ _) hψ_inj (fun p _ => (hψ_step p).2)
  have hφ_id : ∀ p : Idx n, φ p = p := fun p =>
    Prod.ext (Fin.ext (hφ1 p (Finset.mem_univ p))) (Fin.ext (hφ2 p (Finset.mem_univ p)))
  have hψ_id : ∀ p : Idx n, ψ p = p := fun p =>
    Prod.ext (Fin.ext (hψ1 p (Finset.mem_univ p))) (Fin.ext (hψ2 p (Finset.mem_univ p)))
  have hmateA : ∀ p : Idx n, mate hM (embA n p) = embB n p := fun p => by rw [hφ_eq, hφ_id]
  have hmateC : ∀ p : Idx n, mate hM (embC n p) = embD n p := fun p => by rw [hψ_eq, hψ_id]
  have hmateB : ∀ p : Idx n, mate hM (embB n p) = embA n p := fun p => by
    rw [← hmateA p, mate_invol hM]
  have hmateD : ∀ p : Idx n, mate hM (embD n p) = embC n p := fun p => by
    rw [← hmateC p, mate_invol hM]
  apply tiling_ext_mate hM (isDomiculeTiling_M_star n)
  intro v
  rw [mate_M_star]
  rcases board_four_cases v with hv | hv | hv | hv
  · rw [hv, hmateA, muStar_embA]
  · rw [hv, hmateB, muStar_embB]
  · rw [hv, hmateC, muStar_embC]
  · rw [hv, hmateD, muStar_embD]

/-- Dawid Ryłko's first conjecture on `OEIS A401673` (`%F` line 17):
for every `n : ℕ`, `T(n, n^2) = 1` (`2 * n^2` diagonal domicules). -/
theorem domiculeTilings_max_diag_eq_one (n : ℕ) :
    domiculeTilings n (n ^ 2) = 1 := by
  classical
  unfold domiculeTilings
  have hset : ((Finset.univ : Finset (Finset (Sym2 (Board n)))).filter (fun M =>
      IsDomiculeTiling n M ∧ (M.filter (IsDiagDomicule n)).card = 2 * (n ^ 2))) = {M_star n} := by
    ext M
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hM, hcard⟩
      exact eq_M_star_of_max_diag hM hcard
    · rintro rfl
      exact ⟨isDomiculeTiling_M_star n, card_diag_M_star n⟩
  rw [hset, Finset.card_singleton]

/-! ### Section 6 (Steps 5, 6, 7): Proof of Identity 2 (`domiculeTilings_sub_one_diag_eq`) -/

/-- Predicate for a horizontal domino (`r₁ = r₂` and `|c₁ - c₂| = 1`). -/
private def IsHorizDomino (n : ℕ) (e : Sym2 (Board n)) : Prop :=
  ∃ u v, e = s(u, v) ∧ u.1 = v.1 ∧ Nat.dist u.2.val v.2.val = 1

private theorem isHorizDomino_mk {n : ℕ} (u v : Board n) :
    IsHorizDomino n s(u, v) ↔ u.1 = v.1 ∧ Nat.dist u.2.val v.2.val = 1 := by
  constructor
  · rintro ⟨u', v', heq, hr, hc⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hr, hc⟩
    · exact ⟨hr.symm, by rwa [Nat.dist_comm]⟩
  · rintro ⟨hr, hc⟩
    exact ⟨u, v, rfl, hr, hc⟩

/-- Step 7 1D punctured-strip fiber uniqueness (`SCOPING-S017.md` §2.1 Step 7):
any injective map `Φ : Idx n \ {(i_A, j₀)} → Idx n \ {(i_B, j₀)}` (`i_A ≤ i_B`) preserving the
column coordinate and satisfying `(Φ p).1 ≤ p.1 ≤ (Φ p).1 + 1` is uniquely determined on every
column `j ≠ j₀` (`Φ(i, j) = (i, j)`) and on the three intervals `[0, i_A) ⊔ (i_A, i_B] ⊔ (i_B, n)`
of column `j₀`. -/
private theorem punctured_strip_map_unique {n : ℕ} {j₀ i_A i_B : Fin n}
    (hle : i_A.val ≤ i_B.val) {Φ : Idx n → Idx n}
    (hmaps : ∀ p ∈ (Finset.univ : Finset (Idx n)).erase (i_A, j₀),
      Φ p ∈ (Finset.univ : Finset (Idx n)).erase (i_B, j₀))
    (hinj : Set.InjOn Φ ((Finset.univ : Finset (Idx n)).erase (i_A, j₀)))
    (hcol : ∀ p ∈ (Finset.univ : Finset (Idx n)).erase (i_A, j₀), (Φ p).2 = p.2)
    (hrow : ∀ p ∈ (Finset.univ : Finset (Idx n)).erase (i_A, j₀),
      (Φ p).1.val ≤ p.1.val ∧ p.1.val ≤ (Φ p).1.val + 1) :
    ∀ p ∈ (Finset.univ : Finset (Idx n)).erase (i_A, j₀),
      Φ p = if p.2 = j₀ ∧ i_A.val < p.1.val ∧ p.1.val ≤ i_B.val then
        (⟨p.1.val - 1, by omega⟩, p.2)
      else p := by
  have h_other_col : ∀ (j : Fin n), j ≠ j₀ → ∀ i : Fin n, Φ (i, j) = (i, j) := by
    intro j hj
    let f : Fin n → Fin n := fun i => (Φ (i, j)).1
    have hmem : ∀ i : Fin n, (i, j) ∈ (Finset.univ : Finset (Idx n)).erase (i_A, j₀) := by
      intro i
      simp [hj]
    have hf_pair : ∀ i : Fin n, Φ (i, j) = (f i, j) := fun i =>
      Prod.ext rfl (hcol (i, j) (hmem i))
    have hf_inj : Set.InjOn f (Finset.univ : Finset (Fin n)) := by
      intro i₁ _ i₂ _ heq
      have hΦeq : Φ (i₁, j) = Φ (i₂, j) := by rw [hf_pair, hf_pair, heq]
      exact (Prod.mk.inj (hinj (hmem i₁) (hmem i₂) hΦeq)).1
    have hf_le : ∀ i ∈ (Finset.univ : Finset (Fin n)), (f i).val ≤ i.val :=
      fun i _ => (hrow (i, j) (hmem i)).1
    have hf_eq := injOn_endo_eq_of_le (fun i : Fin n => i.val)
      (fun _ _ => Finset.mem_univ _) hf_inj hf_le
    intro i
    rw [hf_pair i]
    exact Prod.ext (Fin.ext (hf_eq i (Finset.mem_univ i))) rfl
  let f : Fin n → Fin n := fun i => (Φ (i, j₀)).1
  have hmem0 : ∀ {i : Fin n}, i ≠ i_A → (i, j₀) ∈ (Finset.univ : Finset (Idx n)).erase (i_A, j₀) := by
    intro i hi
    simp [hi]
  have hf0_pair : ∀ {i : Fin n}, i ≠ i_A → Φ (i, j₀) = (f i, j₀) := fun {i} hi =>
    Prod.ext rfl (hcol (i, j₀) (hmem0 hi))
  have hf0_ne_iB : ∀ {i : Fin n} (hi : i ≠ i_A), f i ≠ i_B := by
    intro i hi hfeq
    have hm := hmaps (i, j₀) (hmem0 hi)
    rw [hf0_pair hi, hfeq] at hm
    exact (Finset.mem_erase.mp hm).1 rfl
  have hf0_inj : Set.InjOn f ((Finset.univ : Finset (Fin n)).erase i_A) := by
    intro i₁ hi₁ i₂ hi₂ heq
    have h1 : i₁ ≠ i_A := (Finset.mem_erase.mp hi₁).1
    have h2 : i₂ ≠ i_A := (Finset.mem_erase.mp hi₂).1
    have hΦeq : Φ (i₁, j₀) = Φ (i₂, j₀) := by rw [hf0_pair h1, hf0_pair h2, heq]
    exact (Prod.mk.inj (hinj (hmem0 h1) (hmem0 h2) hΦeq)).1
  let L : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val < i_A.val)
  have hL_sub : ∀ i ∈ L, i ∈ (Finset.univ : Finset (Fin n)).erase i_A := by
    intro i hi
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_erase.mpr ⟨fun h => by subst h; omega, Finset.mem_univ i⟩
  have hL_maps : ∀ i ∈ L, f i ∈ L := by
    intro i hi
    have hiA : i ≠ i_A := (Finset.mem_erase.mp (hL_sub i hi)).1
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hr := (hrow (i, j₀) (hmem0 hiA)).1
    change (f i).val ≤ i.val at hr
    omega
  have hL_inj : Set.InjOn f L := hf0_inj.mono (fun i hi => hL_sub i hi)
  have hL_eq := injOn_endo_eq_of_le (fun i : Fin n => i.val) hL_maps hL_inj
    (fun i hi => (hrow (i, j₀) (hmem0 (Finset.mem_erase.mp (hL_sub i hi)).1)).1)
  let U : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i_B.val < i.val)
  have hU_sub : ∀ i ∈ U, i ∈ (Finset.univ : Finset (Fin n)).erase i_A := by
    intro i hi
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_erase.mpr ⟨fun h => by subst h; omega, Finset.mem_univ i⟩
  have hU_maps : ∀ i ∈ U, f i ∈ U := by
    intro i hi
    have hiA : i ≠ i_A := (Finset.mem_erase.mp (hU_sub i hi)).1
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hr := (hrow (i, j₀) (hmem0 hiA)).2
    change i.val ≤ (f i).val + 1 at hr
    have hne : (f i).val ≠ i_B.val := fun h => hf0_ne_iB hiA (Fin.ext h)
    omega
  have hU_inj : Set.InjOn f U := hf0_inj.mono (fun i hi => hU_sub i hi)
  have hU_eq := injOn_endo_eq_of_le (fun i : Fin n => i.val) hU_maps hU_inj
    (fun i hi => (hrow (i, j₀) (hmem0 (Finset.mem_erase.mp (hU_sub i hi)).1)).1)
  let M_dom : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => i_A.val < i.val ∧ i.val ≤ i_B.val)
  let M_cod : Finset (Fin n) :=
    Finset.univ.filter (fun k : Fin n => i_A.val ≤ k.val ∧ k.val < i_B.val)
  have hM_sub : ∀ i ∈ M_dom, i ∈ (Finset.univ : Finset (Fin n)).erase i_A := by
    intro i hi
    simp only [M_dom, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_erase.mpr ⟨fun h => by subst h; omega, Finset.mem_univ i⟩
  have hM_maps : ∀ i ∈ M_dom, f i ∈ M_cod := by
    intro i hi
    have hiA : i ≠ i_A := (Finset.mem_erase.mp (hM_sub i hi)).1
    simp only [M_dom, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [M_cod, Finset.mem_filter, Finset.mem_univ, true_and]
    have hr := hrow (i, j₀) (hmem0 hiA)
    change (f i).val ≤ i.val ∧ i.val ≤ (f i).val + 1 at hr
    have hne : (f i).val ≠ i_B.val := fun h => hf0_ne_iB hiA (Fin.ext h)
    omega
  have hM_inj : Set.InjOn f M_dom := hf0_inj.mono (fun i hi => hM_sub i hi)
  let sh : Fin n → Fin n := fun i => ⟨i.val - 1, by omega⟩
  have hsh_maps : ∀ i ∈ M_dom, sh i ∈ M_cod := by
    intro i hi
    simp only [M_dom, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [M_cod, Finset.mem_filter, Finset.mem_univ, true_and, sh]
    omega
  have hsh_inj : Set.InjOn sh M_dom := by
    intro i₁ hi₁ i₂ hi₂ heq
    simp only [Finset.mem_coe, M_dom, Finset.mem_filter, Finset.mem_univ, true_and] at hi₁ hi₂
    have hv := congrArg Fin.val heq
    dsimp only [sh] at hv
    exact Fin.ext (by omega)
  have hM_card : M_cod.card = M_dom.card := by
    symm
    refine Finset.card_bij (fun i _ => sh i) hsh_maps (fun i₁ hi₁ i₂ hi₂ h => hsh_inj hi₁ hi₂ h) ?_
    intro k hk
    simp only [M_cod, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    let i : Fin n := ⟨k.val + 1, by omega⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, by dsimp only [i]; omega⟩, ?_⟩
    exact Fin.ext (by dsimp only [sh, i]; omega)
  have hM_img : M_dom.image f = M_cod :=
    image_eq_of_injOn_of_card_eq hM_maps hM_inj (le_of_eq hM_card)
  have hsh_img : M_dom.image sh = M_cod :=
    image_eq_of_injOn_of_card_eq hsh_maps hsh_inj (le_of_eq hM_card)
  have hsum_f : ∑ i ∈ M_dom, (f i).val = ∑ k ∈ M_cod, k.val := by
    rw [← Finset.sum_image hM_inj, hM_img]
  have hsum_sh : ∑ i ∈ M_dom, (i.val - 1) = ∑ k ∈ M_cod, k.val := by
    change ∑ i ∈ M_dom, (sh i).val = ∑ k ∈ M_cod, k.val
    rw [← Finset.sum_image hsh_inj, hsh_img]
  have hM_add :
      (∑ i ∈ M_dom, ((f i).val - (i.val - 1))) + ∑ i ∈ M_dom, (i.val - 1) =
        ∑ i ∈ M_dom, (f i).val := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hiA : i ≠ i_A := (Finset.mem_erase.mp (hM_sub i hi)).1
    have hr := (hrow (i, j₀) (hmem0 hiA)).2
    change i.val ≤ (f i).val + 1 at hr
    omega
  rw [hsum_f, hsum_sh] at hM_add
  have hM_zero : ∑ i ∈ M_dom, ((f i).val - (i.val - 1)) = 0 := by omega
  have hM_all := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hM_zero
  rintro ⟨i, j⟩ hp
  by_cases hj : j = j₀
  · subst j
    have hiA : i ≠ i_A := fun h => (Finset.mem_erase.mp hp).1 (Prod.ext h rfl)
    have hiA_val : i.val ≠ i_A.val := fun h => hiA (Fin.ext h)
    rw [hf0_pair hiA]
    dsimp only
    by_cases hmid : i_A.val < i.val ∧ i.val ≤ i_B.val
    · have hcond : j₀ = j₀ ∧ i_A.val < i.val ∧ i.val ≤ i_B.val := ⟨rfl, hmid⟩
      rw [ite_eq_left_iff.mpr (fun hn => absurd hcond hn)]
      have hiM : i ∈ M_dom := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmid⟩
      have h0 := hM_all i hiM
      have hr := (hrow (i, j₀) (hmem0 hiA)).2
      change i.val ≤ (f i).val + 1 at hr
      exact Prod.ext (Fin.ext (by change (f i).val = i.val - 1; omega)) rfl
    · have hncond : ¬ (j₀ = j₀ ∧ i_A.val < i.val ∧ i.val ≤ i_B.val) := fun h => hmid h.2
      rw [ite_eq_right_iff.mpr (fun hc => absurd hc hncond)]
      rcases lt_or_gt_of_ne hiA_val with hlt | hgt
      · have hiL : i ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩
        exact Prod.ext (Fin.ext (hL_eq i hiL)) rfl
      · have hgtB : i_B.val < i.val := by omega
        have hiU : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hgtB⟩
        exact Prod.ext (Fin.ext (hU_eq i hiU)) rfl
  · dsimp only
    have hncond : ¬ (j = j₀ ∧ i_A.val < i.val ∧ i.val ≤ i_B.val) := fun h => hj h.1
    rw [ite_eq_right_iff.mpr (fun hc => absurd hc hncond)]
    exact h_other_col j hj i

/-- Row involution inside the defect strip `j₀` (`0 ≤ i_A ≤ i_B < n`). -/
private def rowH {n : ℕ} (i_A i_B : Fin n) (_hle : i_A.val ≤ i_B.val) (r : Fin (2 * n)) :
    Fin (2 * n) :=
  if _h1 : r.val < 2 * i_A.val then flip2 n r
  else if _h2 : r.val = 2 * i_A.val then r
  else if _h3 : r.val < 2 * i_B.val + 1 then
    if _h4 : r.val % 2 = 1 then ⟨r.val + 1, by omega⟩ else ⟨r.val - 1, by omega⟩
  else if _h5 : r.val = 2 * i_B.val + 1 then r
  else flip2 n r

private theorem rowH_lt {n : ℕ} {i_A i_B : Fin n} (hle : i_A.val ≤ i_B.val) {r : Fin (2 * n)}
    (h : r.val < 2 * i_A.val) : rowH i_A i_B hle r = flip2 n r := by
  simp [rowH, h]

private theorem rowH_eq_top {n : ℕ} {i_A i_B : Fin n} (hle : i_A.val ≤ i_B.val) {r : Fin (2 * n)}
    (h : r.val = 2 * i_A.val) : rowH i_A i_B hle r = r := by
  simp [rowH, h]

private theorem rowH_mid_odd {n : ℕ} {i_A i_B : Fin n} (hle : i_A.val ≤ i_B.val) {r : Fin (2 * n)}
    (hlo : 2 * i_A.val < r.val) (hhi : r.val < 2 * i_B.val + 1) (hodd : r.val % 2 = 1) :
    (rowH i_A i_B hle r).val = r.val + 1 := by
  have h1 : ¬ r.val < 2 * i_A.val := by omega
  have h2 : r.val ≠ 2 * i_A.val := by omega
  simp [rowH, h1, h2, hhi, hodd]

private theorem rowH_mid_even {n : ℕ} {i_A i_B : Fin n} (hle : i_A.val ≤ i_B.val) {r : Fin (2 * n)}
    (hlo : 2 * i_A.val < r.val) (hhi : r.val < 2 * i_B.val + 1) (heven : r.val % 2 ≠ 1) :
    (rowH i_A i_B hle r).val = r.val - 1 := by
  have h1 : ¬ r.val < 2 * i_A.val := by omega
  have h2 : r.val ≠ 2 * i_A.val := by omega
  simp [rowH, h1, h2, hhi, heven]

private theorem rowH_eq_bot {n : ℕ} {i_A i_B : Fin n} (hle : i_A.val ≤ i_B.val) {r : Fin (2 * n)}
    (h : r.val = 2 * i_B.val + 1) : rowH i_A i_B hle r = r := by
  unfold rowH
  split_ifs <;> first | rfl | exfalso; omega

private theorem rowH_gt {n : ℕ} {i_A i_B : Fin n} (hle : i_A.val ≤ i_B.val) {r : Fin (2 * n)}
    (h : 2 * i_B.val + 1 < r.val) : rowH i_A i_B hle r = flip2 n r := by
  have h1 : ¬ r.val < 2 * i_A.val := by omega
  have h2 : r.val ≠ 2 * i_A.val := by omega
  have h3 : ¬ r.val < 2 * i_B.val + 1 := by omega
  have h5 : r.val ≠ 2 * i_B.val + 1 := by omega
  simp [rowH, h1, h2, h3, h5]

private theorem rowH_invol {n : ℕ} (i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val) (r : Fin (2 * n)) :
    rowH i_A i_B hle (rowH i_A i_B hle r) = r := by
  by_cases h1 : r.val < 2 * i_A.val
  · rw [rowH_lt hle h1]
    have hdiv := flip2_div n r
    have h1' : (flip2 n r).val < 2 * i_A.val := by omega
    rw [rowH_lt hle h1', flip2_invol]
  · by_cases h2 : r.val = 2 * i_A.val
    · rw [rowH_eq_top hle h2, rowH_eq_top hle h2]
    · have hlo : 2 * i_A.val < r.val := by omega
      by_cases h3 : r.val < 2 * i_B.val + 1
      · by_cases h4 : r.val % 2 = 1
        · have hm1 := rowH_mid_odd hle hlo h3 h4
          have hm2 := rowH_mid_even hle (r := rowH i_A i_B hle r)
            (by omega) (by omega) (by omega)
          exact Fin.ext (by omega)
        · have hm1 := rowH_mid_even hle hlo h3 h4
          have hm2 := rowH_mid_odd hle (r := rowH i_A i_B hle r)
            (by omega) (by omega) (by omega)
          exact Fin.ext (by omega)
      · by_cases h5 : r.val = 2 * i_B.val + 1
        · rw [rowH_eq_bot hle h5, rowH_eq_bot hle h5]
        · have hgt : 2 * i_B.val + 1 < r.val := by omega
          rw [rowH_gt hle hgt]
          have hdiv := flip2_div n r
          have hgt' : 2 * i_B.val + 1 < (flip2 n r).val := by omega
          rw [rowH_gt hle hgt', flip2_invol]

private theorem rowH_dist_le_one {n : ℕ} (i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val)
    (r : Fin (2 * n)) : Nat.dist r.val (rowH i_A i_B hle r).val ≤ 1 := by
  by_cases h1 : r.val < 2 * i_A.val
  · rw [rowH_lt hle h1]; exact le_of_eq (flip2_dist n r)
  · by_cases h2 : r.val = 2 * i_A.val
    · rw [rowH_eq_top hle h2]; simp
    · have hlo : 2 * i_A.val < r.val := by omega
      by_cases h3 : r.val < 2 * i_B.val + 1
      · by_cases h4 : r.val % 2 = 1
        · rw [rowH_mid_odd hle hlo h3 h4, nat_dist_def]; omega
        · rw [rowH_mid_even hle hlo h3 h4, nat_dist_def]; omega
      · by_cases h5 : r.val = 2 * i_B.val + 1
        · rw [rowH_eq_bot hle h5]; simp
        · rw [rowH_gt hle (by omega)]; exact le_of_eq (flip2_dist n r)

private theorem rowH_dist_eq_one_iff {n : ℕ} (i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val)
    (r : Fin (2 * n)) :
    Nat.dist r.val (rowH i_A i_B hle r).val = 1 ↔
      r.val ≠ 2 * i_A.val ∧ r.val ≠ 2 * i_B.val + 1 := by
  by_cases h1 : r.val < 2 * i_A.val
  · rw [rowH_lt hle h1, flip2_dist]; omega
  · by_cases h2 : r.val = 2 * i_A.val
    · rw [rowH_eq_top hle h2, nat_dist_def]; omega
    · have hlo : 2 * i_A.val < r.val := by omega
      by_cases h3 : r.val < 2 * i_B.val + 1
      · by_cases h4 : r.val % 2 = 1
        · rw [rowH_mid_odd hle hlo h3 h4, nat_dist_def]; omega
        · rw [rowH_mid_even hle hlo h3 h4, nat_dist_def]; omega
      · by_cases h5 : r.val = 2 * i_B.val + 1
        · rw [rowH_eq_bot hle h5, nat_dist_def]; omega
        · have hgt : 2 * i_B.val + 1 < r.val := by omega
          rw [rowH_gt hle hgt, flip2_dist]; omega

/-- Explicit involution for the horizontal-defect matching `constructH n j₀ i_A i_B`. -/
private def muH {n : ℕ} (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val) (v : Board n) : Board n :=
  if v.2.val / 2 = j₀.val then (rowH i_A i_B hle v.1, flip2 n v.2)
  else muStar n v

private theorem muH_invol {n : ℕ} (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val) (v : Board n) :
    muH j₀ i_A i_B hle (muH j₀ i_A i_B hle v) = v := by
  have hdiv : (flip2 n v.2).val / 2 = v.2.val / 2 := flip2_div n v.2
  by_cases hj : v.2.val / 2 = j₀.val
  · simp [muH, hj, hdiv, rowH_invol, flip2_invol]
  · simp [muH, muStar, hj, hdiv, flip2_invol]

private theorem muH_kingAdj {n : ℕ} (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val) (v : Board n) :
    kingAdj n v (muH j₀ i_A i_B hle v) := by
  by_cases hj : v.2.val / 2 = j₀.val
  · simp only [muH, hj, ↓reduceIte]
    have hd2 : Nat.dist v.2.val (flip2 n v.2).val = 1 := flip2_dist n v.2
    refine ⟨?_, rowH_dist_le_one i_A i_B hle v.1, le_of_eq hd2⟩
    intro heq
    have hc := congrArg (fun x : Board n => x.2.val) heq
    dsimp only at hc
    rw [← hc, nat_dist_def] at hd2
    omega
  · simp only [muH, hj, ↓reduceIte]
    exact muStar_kingAdj n v

/-- Explicit Case-H matching `constructH n j₀ i_A i_B` (`SCOPING-S017.md` §5.2). -/
def constructH (n : ℕ) (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val) :
    Finset (Sym2 (Board n)) :=
  matchingOfInvolution n (muH j₀ i_A i_B hle)

theorem isDomiculeTiling_constructH {n : ℕ} (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val) :
    IsDomiculeTiling n (constructH n j₀ i_A i_B hle) :=
  isDomiculeTiling_of_invol (muH_invol j₀ i_A i_B hle) (muH_kingAdj j₀ i_A i_B hle)

private theorem mate_constructH {n : ℕ} (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val)
    (v : Board n) :
    mate (isDomiculeTiling_constructH j₀ i_A i_B hle) v = muH j₀ i_A i_B hle v :=
  mate_matchingOfInvolution (muH_invol j₀ i_A i_B hle) (muH_kingAdj j₀ i_A i_B hle) v

private theorem muH_embA_diagAdj_iff {n : ℕ} (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val)
    (p : Idx n) :
    diagAdj n (embA n p) (muH j₀ i_A i_B hle (embA n p)) ↔ p ≠ (i_A, j₀) := by
  rcases p with ⟨i, j⟩
  by_cases hj : j = j₀
  · subst j
    have hdiv : (embA n (i, j₀)).2.val / 2 = j₀.val := by simp [embA]
    simp only [muH, hdiv, ↓reduceIte, diagAdj, flip2_dist, and_true, rowH_dist_eq_one_iff]
    simp only [embA]
    constructor
    · intro h heq
      have hi : i = i_A := (Prod.mk.inj heq).1
      exact h.1 (by rw [hi])
    · intro hne
      refine ⟨fun hr => hne (Prod.ext (Fin.ext ?_) rfl), by omega⟩
      change 2 * i.val = 2 * i_A.val at hr
      change i.val = i_A.val
      omega
  · have hdiv : (embA n (i, j)).2.val / 2 ≠ j₀.val := by
      simp only [embA]
      intro h
      exact hj (Fin.ext (by omega))
    simp only [muH, hdiv, ↓reduceIte]
    exact ⟨fun _ heq => hj (Prod.mk.inj heq).2, fun _ => muStar_diagAdj n (embA n (i, j))⟩

private theorem muH_embB_diagAdj_iff {n : ℕ} (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val)
    (p : Idx n) :
    diagAdj n (embB n p) (muH j₀ i_A i_B hle (embB n p)) ↔ p ≠ (i_B, j₀) := by
  rcases p with ⟨i, j⟩
  by_cases hj : j = j₀
  · subst j
    have hdiv : (embB n (i, j₀)).2.val / 2 = j₀.val := by simp only [embB]; omega
    simp only [muH, hdiv, ↓reduceIte, diagAdj, flip2_dist, and_true, rowH_dist_eq_one_iff]
    simp only [embB]
    constructor
    · intro h heq
      have hi : i = i_B := (Prod.mk.inj heq).1
      exact h.2 (by rw [hi])
    · intro hne
      refine ⟨by omega, fun hr => hne (Prod.ext (Fin.ext ?_) rfl)⟩
      change 2 * i.val + 1 = 2 * i_B.val + 1 at hr
      change i.val = i_B.val
      omega
  · have hdiv : (embB n (i, j)).2.val / 2 ≠ j₀.val := by
      simp only [embB]
      intro h
      exact hj (Fin.ext (by omega))
    simp only [muH, hdiv, ↓reduceIte]
    exact ⟨fun _ heq => hj (Prod.mk.inj heq).2, fun _ => muStar_diagAdj n (embB n (i, j))⟩

private theorem muH_embA_apply {n : ℕ} (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val) (p : Idx n) :
    muH j₀ i_A i_B hle (embA n p) =
      if p = (i_A, j₀) then embC n (i_A, j₀)
      else if p.2 = j₀ ∧ i_A.val < p.1.val ∧ p.1.val ≤ i_B.val then
        embB n (⟨p.1.val - 1, by omega⟩, p.2)
      else embB n p := by
  rcases p with ⟨i, j⟩
  by_cases hj : j = j₀
  · subst j
    have hdiv : (embA n (i, j₀)).2.val / 2 = j₀.val := by simp [embA]
    have hcol : flip2 n (embA n (i, j₀)).2 = ⟨2 * j₀.val + 1, by omega⟩ := by
      refine Fin.ext ?_
      change (flip2 n (embA n (i, j₀)).2).val = 2 * j₀.val + 1
      rw [flip2_val_of_even (by simp [embA])]
      simp [embA]
    by_cases hi : i = i_A
    · subst i
      simp only [↓reduceIte, muH, hdiv, hcol]
      refine Prod.ext ?_ rfl
      exact rowH_eq_top hle (by simp [embA])
    · have hne : (i, j₀) ≠ (i_A, j₀) := fun h => hi (Prod.mk.inj h).1
      have hi_val : i.val ≠ i_A.val := fun h => hi (Fin.ext h)
      rw [ite_eq_right_iff.mpr (fun hc => absurd hc hne)]
      dsimp only
      by_cases hmid : i_A.val < i.val ∧ i.val ≤ i_B.val
      · have hcond : j₀ = j₀ ∧ i_A.val < i.val ∧ i.val ≤ i_B.val := ⟨rfl, hmid⟩
        rw [ite_eq_left_iff.mpr (fun hn => absurd hcond hn)]
        simp only [muH, hdiv, ↓reduceIte, hcol]
        refine Prod.ext (Fin.ext ?_) (by simp [embB])
        rw [rowH_mid_even hle (by simp only [embA]; omega) (by simp only [embA]; omega)
          (by simp only [embA]; omega)]
        simp only [embA, embB]
        omega
      · have hncond : ¬ (j₀ = j₀ ∧ i_A.val < i.val ∧ i.val ≤ i_B.val) := fun h => hmid h.2
        rw [ite_eq_right_iff.mpr (fun hc => absurd hc hncond)]
        simp only [muH, hdiv, ↓reduceIte, hcol]
        refine Prod.ext (Fin.ext ?_) (by simp [embB])
        rcases lt_or_gt_of_ne hi_val with hlt | hgt
        · rw [rowH_lt hle (by simp only [embA]; omega),
            flip2_val_of_even (by simp [embA])]
          simp [embA, embB]
        · have hgtB : i_B.val < i.val := by omega
          rw [rowH_gt hle (by simp only [embA]; omega),
            flip2_val_of_even (by simp [embA])]
          simp [embA, embB]
  · have hdiv : (embA n (i, j)).2.val / 2 ≠ j₀.val := by
      simp only [embA]
      intro h
      exact hj (Fin.ext (by omega))
    have hne : (i, j) ≠ (i_A, j₀) := fun h => hj (Prod.mk.inj h).2
    rw [ite_eq_right_iff.mpr (fun hc => absurd hc hne)]
    dsimp only
    have hncond : ¬ (j = j₀ ∧ i_A.val < i.val ∧ i.val ≤ i_B.val) := fun h => hj h.1
    rw [ite_eq_right_iff.mpr (fun hc => absurd hc hncond)]
    simp only [muH, hdiv, ↓reduceIte, muStar_embA]

private theorem muH_embC_apply {n : ℕ} (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val) (p : Idx n) :
    muH j₀ i_A i_B hle (embC n p) =
      if p = (i_A, j₀) then embA n (i_A, j₀)
      else if p.2 = j₀ ∧ i_A.val < p.1.val ∧ p.1.val ≤ i_B.val then
        embD n (⟨p.1.val - 1, by omega⟩, p.2)
      else embD n p := by
  rcases p with ⟨i, j⟩
  by_cases hj : j = j₀
  · subst j
    have hdiv : (embC n (i, j₀)).2.val / 2 = j₀.val := by simp only [embC]; omega
    have hcol : flip2 n (embC n (i, j₀)).2 = ⟨2 * j₀.val, by omega⟩ := by
      refine Fin.ext ?_
      change (flip2 n (embC n (i, j₀)).2).val = 2 * j₀.val
      rw [flip2_val_of_odd (by simp only [embC]; omega)]
      simp [embC]
    by_cases hi : i = i_A
    · subst i
      simp only [↓reduceIte, muH, hdiv, hcol]
      refine Prod.ext ?_ rfl
      exact rowH_eq_top hle (by simp [embC])
    · have hne : (i, j₀) ≠ (i_A, j₀) := fun h => hi (Prod.mk.inj h).1
      have hi_val : i.val ≠ i_A.val := fun h => hi (Fin.ext h)
      rw [ite_eq_right_iff.mpr (fun hc => absurd hc hne)]
      dsimp only
      by_cases hmid : i_A.val < i.val ∧ i.val ≤ i_B.val
      · have hcond : j₀ = j₀ ∧ i_A.val < i.val ∧ i.val ≤ i_B.val := ⟨rfl, hmid⟩
        rw [ite_eq_left_iff.mpr (fun hn => absurd hcond hn)]
        simp only [muH, hdiv, ↓reduceIte, hcol]
        refine Prod.ext (Fin.ext ?_) (by simp [embD])
        rw [rowH_mid_even hle (by simp only [embC]; omega) (by simp only [embC]; omega)
          (by simp only [embC]; omega)]
        simp only [embC, embD]
        omega
      · have hncond : ¬ (j₀ = j₀ ∧ i_A.val < i.val ∧ i.val ≤ i_B.val) := fun h => hmid h.2
        rw [ite_eq_right_iff.mpr (fun hc => absurd hc hncond)]
        simp only [muH, hdiv, ↓reduceIte, hcol]
        refine Prod.ext (Fin.ext ?_) (by simp [embD])
        rcases lt_or_gt_of_ne hi_val with hlt | hgt
        · rw [rowH_lt hle (by simp only [embC]; omega),
            flip2_val_of_even (by simp [embC])]
          simp [embC, embD]
        · have hgtB : i_B.val < i.val := by omega
          rw [rowH_gt hle (by simp only [embC]; omega),
            flip2_val_of_even (by simp [embC])]
          simp [embC, embD]
  · have hdiv : (embC n (i, j)).2.val / 2 ≠ j₀.val := by
      simp only [embC]
      intro h
      exact hj (Fin.ext (by omega))
    have hne : (i, j) ≠ (i_A, j₀) := fun h => hj (Prod.mk.inj h).2
    rw [ite_eq_right_iff.mpr (fun hc => absurd hc hne)]
    dsimp only
    have hncond : ¬ (j = j₀ ∧ i_A.val < i.val ∧ i.val ≤ i_B.val) := fun h => hj h.1
    rw [ite_eq_right_iff.mpr (fun hc => absurd hc hncond)]
    simp only [↓reduceIte, muH, hdiv, muStar_embC]

private theorem muH_embB_defect {n : ℕ} (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val) :
    muH j₀ i_A i_B hle (embB n (i_B, j₀)) = embD n (i_B, j₀) := by
  have hdiv : (embB n (i_B, j₀)).2.val / 2 = j₀.val := by simp only [embB]; omega
  simp only [muH, hdiv, ↓reduceIte]
  refine Prod.ext ?_ (Fin.ext ?_)
  · exact rowH_eq_bot hle (by simp [embB])
  · change (flip2 n (embB n (i_B, j₀)).2).val = 2 * j₀.val
    rw [flip2_val_of_odd (by simp only [embB]; omega)]
    simp [embB]

private theorem constructH_injective {n : ℕ} {j₀ i_A i_B j₀' i_A' i_B' : Fin n}
    (hle : i_A.val ≤ i_B.val) (hle' : i_A'.val ≤ i_B'.val)
    (heq : constructH n j₀ i_A i_B hle = constructH n j₀' i_A' i_B' hle') :
    j₀ = j₀' ∧ i_A = i_A' ∧ i_B = i_B' := by
  have hM := isDomiculeTiling_constructH j₀ i_A i_B hle
  have hM' := isDomiculeTiling_constructH j₀' i_A' i_B' hle'
  have heq_mate : ∀ v, muH j₀ i_A i_B hle v = muH j₀' i_A' i_B' hle' v := by
    intro v
    rw [← mate_constructH j₀ i_A i_B hle v, ← mate_constructH j₀' i_A' i_B' hle' v]
    symm
    apply (mk_mem_iff_mate hM' v (mate hM v)).mp
    rw [← heq]
    exact mk_mate_mem hM v
  have hA : ¬ diagAdj n (embA n (i_A, j₀)) (muH j₀' i_A' i_B' hle' (embA n (i_A, j₀))) := by
    rw [← heq_mate]
    exact (muH_embA_diagAdj_iff j₀ i_A i_B hle (i_A, j₀)).not.mpr (not_not.mpr rfl)
  have hpA : (i_A, j₀) = (i_A', j₀') := by
    by_contra hne
    exact hA ((muH_embA_diagAdj_iff j₀' i_A' i_B' hle' (i_A, j₀)).mpr hne)
  have hB : ¬ diagAdj n (embB n (i_B, j₀)) (muH j₀' i_A' i_B' hle' (embB n (i_B, j₀))) := by
    rw [← heq_mate]
    exact (muH_embB_diagAdj_iff j₀ i_A i_B hle (i_B, j₀)).not.mpr (not_not.mpr rfl)
  have hpB : (i_B, j₀) = (i_B', j₀') := by
    by_contra hne
    exact hB ((muH_embB_diagAdj_iff j₀' i_A' i_B' hle' (i_B, j₀)).mpr hne)
  exact ⟨(Prod.mk.inj hpA).2, (Prod.mk.inj hpA).1, (Prod.mk.inj hpB).1⟩

section SubOne

open scoped Classical

/-- Set of one-defect (`2 * (n^2 - 1)` diagonal domicules) tilings, split into `F_H` and `F_V`. -/
noncomputable def subOneTilings (n : ℕ) : Finset (Finset (Sym2 (Board n))) :=
  (Finset.univ : Finset (Finset (Sym2 (Board n)))).filter (fun M =>
    IsDomiculeTiling n M ∧ (M.filter (IsDiagDomicule n)).card = 2 * (n ^ 2 - 1))

noncomputable def F_H (n : ℕ) : Finset (Finset (Sym2 (Board n))) :=
  (subOneTilings n).filter (fun M => ∃ e ∈ M, IsHorizDomino n e)

noncomputable def F_V (n : ℕ) : Finset (Finset (Sym2 (Board n))) :=
  (subOneTilings n).filter (fun M => ¬ ∃ e ∈ M, IsHorizDomino n e)

private theorem domiculeTilings_sub_one_eq_FH_add_FV (n : ℕ) :
    domiculeTilings n (n ^ 2 - 1) = (F_H n).card + (F_V n).card := by
  unfold domiculeTilings F_H F_V subOneTilings
  exact (Finset.card_filter_add_card_filter_not (fun M => ∃ e ∈ M, IsHorizDomino n e)).symm

/-- Step 5 orthogonal-pair dichotomy: in any `2 * (n^2 - 1)`-diagonal tiling (`1 ≤ n`), each class
`A, B, C, D` has a unique non-diagonal index `p_A, p_B, p_C, p_D`, and either `A—C, B—D` (Case H,
iff `∃ e ∈ M, IsHorizDomino n e`) or `A—D, B—C` (Case V, iff `¬ ∃ e ∈ M, IsHorizDomino n e`). -/
private theorem one_defect_dichotomy {n : ℕ} (hn : 1 ≤ n) {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M)
    (hcard : (M.filter (IsDiagDomicule n)).card = 2 * (n ^ 2 - 1)) :
    ∃ p_A p_B p_C p_D : Idx n,
      orthIdxA hM = {p_A} ∧ orthIdxB hM = {p_B} ∧
      orthIdxC hM = {p_C} ∧ orthIdxD hM = {p_D} ∧
      ((mate hM (embA n p_A) = embC n p_C ∧ mate hM (embB n p_B) = embD n p_D ∧
          (∃ e ∈ M, IsHorizDomino n e)) ∨
        (mate hM (embA n p_A) = embD n p_D ∧ mate hM (embB n p_B) = embC n p_C ∧
          ¬ (∃ e ∈ M, IsHorizDomino n e))) := by
  have hn2 : 1 ≤ n ^ 2 := by
    have : 1 * 1 ≤ n * n := Nat.mul_le_mul hn hn
    simpa [pow_two] using this
  have hdA : (diagIdxA hM).card = n ^ 2 - 1 := by
    have := filter_diag_card_eq_two_mul hM
    omega
  have hdB : (diagIdxB hM).card = n ^ 2 - 1 := (card_diagIdxB_eq hM).trans hdA
  have hdC : (diagIdxC hM).card = n ^ 2 - 1 := (card_diagIdxA_eq_diagIdxC hM).symm.trans hdA
  have hdD : (diagIdxD hM).card = n ^ 2 - 1 := (card_diagIdxD_eq hM).trans hdC
  have hoA : (orthIdxA hM).card = 1 := by have := card_diag_add_orth_A hM; omega
  have hoB : (orthIdxB hM).card = 1 := by have := card_diag_add_orth_B hM; omega
  have hoC : (orthIdxC hM).card = 1 := by have := card_diag_add_orth_C hM; omega
  have hoD : (orthIdxD hM).card = 1 := by have := card_diag_add_orth_D hM; omega
  obtain ⟨p_A, hpA⟩ := Finset.card_eq_one.mp hoA
  obtain ⟨p_B, hpB⟩ := Finset.card_eq_one.mp hoB
  obtain ⟨p_C, hpC⟩ := Finset.card_eq_one.mp hoC
  obtain ⟨p_D, hpD⟩ := Finset.card_eq_one.mp hoD
  refine ⟨p_A, p_B, p_C, p_D, hpA, hpB, hpC, hpD, ?_⟩
  have hmemA : p_A ∈ orthIdxA hM := hpA ▸ Finset.mem_singleton_self p_A
  have hmemB : p_B ∈ orthIdxB hM := hpB ▸ Finset.mem_singleton_self p_B
  simp only [orthIdxA, orthIdxB, Finset.mem_filter, Finset.mem_univ, true_and] at hmemA hmemB
  have hmate_in_CD : ∀ v : Board n, (v.1.val + v.2.val) % 2 = 0 → ¬ diagAdj n v (mate hM v) →
      mate hM v = embC n p_C ∨ mate hM v = embD n p_D := by
    intro v hpar0 hnd
    have hflip := orth_parity_flip (kingAdj_mate hM v) hnd
    have hpar1 : ((mate hM v).1.val + (mate hM v).2.val) % 2 = 1 := by omega
    have hnd_mate : ¬ diagAdj n (mate hM v) (mate hM (mate hM v)) := by
      rw [mate_invol hM]
      exact fun hd => hnd (diagAdj_symm hd)
    rcases board_four_cases (mate hM v) with hw | hw | hw | hw
    · exfalso; rw [hw] at hpar1; simp only [embA] at hpar1; omega
    · exfalso; rw [hw] at hpar1; simp only [embB] at hpar1; omega
    · left
      have hq : blk n (mate hM v) ∈ orthIdxC hM := by
        simp only [orthIdxC, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [← hw]
      rw [hpC, Finset.mem_singleton] at hq
      rwa [hq] at hw
    · right
      have hq : blk n (mate hM v) ∈ orthIdxD hM := by
        simp only [orthIdxD, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [← hw]
      rw [hpD, Finset.mem_singleton] at hq
      rwa [hq] at hw
  have hA_cases := hmate_in_CD (embA n p_A) (by simp only [embA]; omega) hmemA
  have hB_cases := hmate_in_CD (embB n p_B) (by simp only [embB]; omega) hmemB
  have hAB_ne : mate hM (embA n p_A) ≠ mate hM (embB n p_B) := by
    intro heq
    have := mate_injective hM heq
    have hr := congrArg (fun x : Board n => x.1.val) this
    simp only [embA, embB] at hr
    omega
  rcases hA_cases with hAC | hAD
  · left
    have hBD : mate hM (embB n p_B) = embD n p_D := by
      rcases hB_cases with hBC | hBD
      · exfalso; exact hAB_ne (hAC.trans hBC.symm)
      · exact hBD
    refine ⟨hAC, hBD, ?_⟩
    refine ⟨s(embA n p_A, embC n p_C), (mk_mem_iff_mate hM _ _).mpr hAC, ?_⟩
    rw [isHorizDomino_mk]
    have hk : kingAdj n (embA n p_A) (embC n p_C) := hAC ▸ kingAdj_mate hM (embA n p_A)
    obtain ⟨hq1, hlo, hhi⟩ := (kingAdj_embA_embC_iff p_A p_C).mp hk
    refine ⟨?_, ?_⟩
    · simp [embA, embC, hq1]
    · simp only [embA, embC, nat_dist_def]
      omega
  · right
    have hBC : mate hM (embB n p_B) = embC n p_C := by
      rcases hB_cases with hBC | hBD
      · exact hBC
      · exfalso; exact hAB_ne (hAD.trans hBD.symm)
    refine ⟨hAD, hBC, ?_⟩
    rintro ⟨e, heM, hhoriz⟩
    refine Sym2.ind (fun u v => ?_) e heM hhoriz
    intro heM hhoriz
    rw [isHorizDomino_mk] at hhoriz
    have hmu : mate hM u = v := (mk_mem_iff_mate hM u v).mp heM
    have hnd : ¬ diagAdj n u (mate hM u) := by
      rw [hmu]
      intro hd
      have h1 := hd.1
      rw [hhoriz.1, nat_dist_def] at h1
      omega
    rcases board_four_cases u with hu | hu | hu | hu
    · have hp : blk n u ∈ orthIdxA hM := by
        simp only [orthIdxA, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [← hu]
      rw [hpA, Finset.mem_singleton] at hp
      rw [hp] at hu
      have hv : v = embD n p_D := by rw [← hmu, hu, hAD]
      have hr := congrArg Fin.val hhoriz.1
      rw [hu, hv] at hr
      simp only [embA, embD] at hr
      omega
    · have hp : blk n u ∈ orthIdxB hM := by
        simp only [orthIdxB, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [← hu]
      rw [hpB, Finset.mem_singleton] at hp
      rw [hp] at hu
      have hv : v = embC n p_C := by rw [← hmu, hu, hBC]
      have hr := congrArg Fin.val hhoriz.1
      rw [hu, hv] at hr
      simp only [embB, embC] at hr
      omega
    · have hp : blk n u ∈ orthIdxC hM := by
        simp only [orthIdxC, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [← hu]
      rw [hpC, Finset.mem_singleton] at hp
      rw [hp] at hu
      have hv : v = embB n p_B := by rw [← hmu, hu, ← hBC, mate_invol hM]
      have hr := congrArg Fin.val hhoriz.1
      rw [hu, hv] at hr
      simp only [embC, embB] at hr
      omega
    · have hp : blk n u ∈ orthIdxD hM := by
        simp only [orthIdxD, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [← hu]
      rw [hpD, Finset.mem_singleton] at hp
      rw [hp] at hu
      have hv : v = embA n p_A := by rw [← hmu, hu, ← hAD, mate_invol hM]
      have hr := congrArg Fin.val hhoriz.1
      rw [hu, hv] at hr
      simp only [embD, embA] at hr
      omega

/-- Cell transpose `(r, c) ↦ (c, r)` on matchings (`Step 5: F_H ≃ F_V`). -/
private def transposeMatching (n : ℕ) (M : Finset (Sym2 (Board n))) : Finset (Sym2 (Board n)) :=
  M.image (Sym2.map Prod.swap)

private theorem sym2_swap_invol (n : ℕ) (e : Sym2 (Board n)) :
    Sym2.map Prod.swap (Sym2.map Prod.swap e) = e := by
  refine Sym2.ind (fun u v => ?_) e
  rfl

private theorem sym2_swap_injective (n : ℕ) :
    Function.Injective (Sym2.map (Prod.swap : Board n → Board n)) :=
  Function.Involutive.injective (sym2_swap_invol n)

private theorem transposeMatching_invol (n : ℕ) (M : Finset (Sym2 (Board n))) :
    transposeMatching n (transposeMatching n M) = M := by
  unfold transposeMatching
  rw [Finset.image_image]
  ext e
  simp [sym2_swap_invol]

private theorem mem_transposeMatching_iff (n : ℕ) (M : Finset (Sym2 (Board n))) (e : Sym2 (Board n)) :
    e ∈ transposeMatching n M ↔ Sym2.map Prod.swap e ∈ M := by
  unfold transposeMatching
  rw [Finset.mem_image]
  constructor
  · rintro ⟨e', he', rfl⟩
    rwa [sym2_swap_invol]
  · intro he
    exact ⟨Sym2.map Prod.swap e, he, sym2_swap_invol n e⟩

private theorem kingAdj_swap_iff (n : ℕ) (u v : Board n) :
    kingAdj n u.swap v.swap ↔ kingAdj n u v := by
  simp only [kingAdj, Prod.swap]
  refine ⟨fun ⟨hne, h1, h2⟩ => ⟨fun h => hne (by rw [h]), h2, h1⟩,
    fun ⟨hne, h1, h2⟩ => ⟨fun h => hne (Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1), h2, h1⟩⟩

private theorem diagAdj_swap_iff (n : ℕ) (u v : Board n) :
    diagAdj n u.swap v.swap ↔ diagAdj n u v := by
  simp only [diagAdj, Prod.swap]
  exact and_comm

private theorem isDiagDomicule_swap_iff (n : ℕ) (e : Sym2 (Board n)) :
    IsDiagDomicule n (Sym2.map Prod.swap e) ↔ IsDiagDomicule n e := by
  refine Sym2.ind (fun u v => ?_) e
  change IsDiagDomicule n s(u.swap, v.swap) ↔ IsDiagDomicule n s(u, v)
  rw [isDiagDomicule_mk, isDiagDomicule_mk, diagAdj_swap_iff]

private theorem mem_sym2_swap_iff {n : ℕ} (v : Board n) (e : Sym2 (Board n)) :
    v ∈ Sym2.map Prod.swap e ↔ v.swap ∈ e := by
  refine Sym2.ind (fun a b => ?_) e
  change v ∈ s(a.swap, b.swap) ↔ v.swap ∈ s(a, b)
  simp only [Sym2.mem_iff]
  constructor <;> rintro (h | h)
  · left; rw [h, Prod.swap_swap]
  · right; rw [h, Prod.swap_swap]
  · left; rw [← h, Prod.swap_swap]
  · right; rw [← h, Prod.swap_swap]

private theorem isDomiculeTiling_transpose {n : ℕ} {M : Finset (Sym2 (Board n))}
    (hM : IsDomiculeTiling n M) : IsDomiculeTiling n (transposeMatching n M) := by
  constructor
  · intro e he
    rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
    refine Sym2.ind (fun u v => ?_) e' he'
    intro he'
    have hk : kingAdj n u v := (hM.1 s(u, v) he').2 u v rfl
    exact edge_valid_mk ((kingAdj_swap_iff n u v).mpr hk)
  · intro v
    obtain ⟨e', ⟨he'M, hv'⟩, huniq⟩ := hM.2 v.swap
    refine ⟨Sym2.map Prod.swap e',
      ⟨Finset.mem_image_of_mem _ he'M, (mem_sym2_swap_iff v e').mpr hv'⟩, ?_⟩
    rintro e ⟨he, hve⟩
    have he_sw : Sym2.map Prod.swap e ∈ M := (mem_transposeMatching_iff n M e).mp he
    have hve_sw : v.swap ∈ Sym2.map Prod.swap e := by
      rw [mem_sym2_swap_iff, Prod.swap_swap]
      exact hve
    have h1 := huniq (Sym2.map Prod.swap e) ⟨he_sw, hve_sw⟩
    calc
      e = Sym2.map Prod.swap (Sym2.map Prod.swap e) := (sym2_swap_invol n e).symm
      _ = Sym2.map Prod.swap e' := by rw [h1]

private theorem card_diag_transpose (n : ℕ) (M : Finset (Sym2 (Board n))) :
    ((transposeMatching n M).filter (IsDiagDomicule n)).card =
      (M.filter (IsDiagDomicule n)).card := by
  refine Finset.card_bij (fun e _ => Sym2.map Prod.swap e) ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨(mem_transposeMatching_iff n M e).mp he.1, (isDiagDomicule_swap_iff n _).mpr he.2⟩
  · intro e₁ _ e₂ _ heq
    exact sym2_swap_injective n heq
  · intro e' he'
    simp only [Finset.mem_filter] at he'
    refine ⟨Sym2.map Prod.swap e', ?_, sym2_swap_invol n e'⟩
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_image_of_mem _ he'.1, (isDiagDomicule_swap_iff n e').mpr he'.2⟩

private theorem transpose_mem_FV_of_mem_FH {n : ℕ} (hn : 1 ≤ n) {M : Finset (Sym2 (Board n))}
    (hM_FH : M ∈ F_H n) : transposeMatching n M ∈ F_V n := by
  simp only [F_H, F_V, subOneTilings, Finset.mem_filter, Finset.mem_univ, true_and] at hM_FH ⊢
  rcases hM_FH with ⟨⟨hM, hcard⟩, hhoriz⟩
  refine ⟨⟨isDomiculeTiling_transpose hM, by rw [card_diag_transpose, hcard]⟩, ?_⟩
  obtain ⟨p_A, p_B, p_C, p_D, hpA, hpB, hpC, hpD, hdich⟩ := one_defect_dichotomy hn hM hcard
  rcases hdich with ⟨hAC, hBD, _⟩ | ⟨_, _, hno⟩
  · rintro ⟨e, he_tr, hhoriz_e⟩
    refine Sym2.ind (fun u v => ?_) e he_tr hhoriz_e
    intro he_tr hhoriz_e
    rw [isHorizDomino_mk] at hhoriz_e
    have heM : s(u.swap, v.swap) ∈ M := (mem_transposeMatching_iff n M s(u, v)).mp he_tr
    have hmu : mate hM u.swap = v.swap := (mk_mem_iff_mate hM u.swap v.swap).mp heM
    have hcol_eq : u.swap.2 = v.swap.2 := hhoriz_e.1
    have hnd : ¬ diagAdj n u.swap (mate hM u.swap) := by
      rw [hmu]
      intro hd
      have h2 := hd.2
      rw [hcol_eq, nat_dist_def] at h2
      omega
    rcases board_four_cases u.swap with hu | hu | hu | hu
    · have hp : blk n u.swap ∈ orthIdxA hM := by
        simp only [orthIdxA, Finset.mem_filter, Finset.mem_univ, true_and]; rwa [← hu]
      rw [hpA, Finset.mem_singleton] at hp; rw [hp] at hu
      have hv : v.swap = embC n p_C := by rw [← hmu, hu, hAC]
      have hc := congrArg Fin.val hcol_eq; rw [hu, hv] at hc; simp only [embA, embC] at hc; omega
    · have hp : blk n u.swap ∈ orthIdxB hM := by
        simp only [orthIdxB, Finset.mem_filter, Finset.mem_univ, true_and]; rwa [← hu]
      rw [hpB, Finset.mem_singleton] at hp; rw [hp] at hu
      have hv : v.swap = embD n p_D := by rw [← hmu, hu, hBD]
      have hc := congrArg Fin.val hcol_eq; rw [hu, hv] at hc; simp only [embB, embD] at hc; omega
    · have hp : blk n u.swap ∈ orthIdxC hM := by
        simp only [orthIdxC, Finset.mem_filter, Finset.mem_univ, true_and]; rwa [← hu]
      rw [hpC, Finset.mem_singleton] at hp; rw [hp] at hu
      have hv : v.swap = embA n p_A := by rw [← hmu, hu, ← hAC, mate_invol hM]
      have hc := congrArg Fin.val hcol_eq; rw [hu, hv] at hc; simp only [embC, embA] at hc; omega
    · have hp : blk n u.swap ∈ orthIdxD hM := by
        simp only [orthIdxD, Finset.mem_filter, Finset.mem_univ, true_and]; rwa [← hu]
      rw [hpD, Finset.mem_singleton] at hp; rw [hp] at hu
      have hv : v.swap = embB n p_B := by rw [← hmu, hu, ← hBD, mate_invol hM]
      have hc := congrArg Fin.val hcol_eq; rw [hu, hv] at hc; simp only [embD, embB] at hc; omega
  · exact absurd hhoriz hno

private theorem transpose_mem_FH_of_mem_FV {n : ℕ} (hn : 1 ≤ n) {M : Finset (Sym2 (Board n))}
    (hM_FV : M ∈ F_V n) : transposeMatching n M ∈ F_H n := by
  simp only [F_H, F_V, subOneTilings, Finset.mem_filter, Finset.mem_univ, true_and] at hM_FV ⊢
  rcases hM_FV with ⟨⟨hM, hcard⟩, hno⟩
  refine ⟨⟨isDomiculeTiling_transpose hM, by rw [card_diag_transpose, hcard]⟩, ?_⟩
  obtain ⟨p_A, p_B, p_C, p_D, _, _, _, _, hdich⟩ := one_defect_dichotomy hn hM hcard
  rcases hdich with ⟨_, _, hhoriz⟩ | ⟨hAD, _, _⟩
  · exact absurd hhoriz hno
  · have heM : s(embA n p_A, embD n p_D) ∈ M := (mk_mem_iff_mate hM _ _).mpr hAD
    have hk : kingAdj n (embA n p_A) (embD n p_D) := hAD ▸ kingAdj_mate hM (embA n p_A)
    rcases hk with ⟨_, h1, h2⟩
    simp only [embA, embD, nat_dist_def] at h1 h2
    refine ⟨s((embA n p_A).swap, (embD n p_D).swap),
      Finset.mem_image_of_mem (Sym2.map Prod.swap) heM, ?_⟩
    rw [isHorizDomino_mk]
    refine ⟨Fin.ext (by simp only [Prod.swap, embA, embD]; omega), ?_⟩
    simp only [Prod.swap, embA, embD, nat_dist_def]
    omega

/-- Step 5 transpose bijection: `(F_V n).card = (F_H n).card` for every `1 ≤ n`. -/
private theorem card_FV_eq_card_FH {n : ℕ} (hn : 1 ≤ n) : (F_V n).card = (F_H n).card := by
  symm
  refine Finset.card_bij (fun M _ => transposeMatching n M) ?_ ?_ ?_
  · intro M hM
    exact transpose_mem_FV_of_mem_FH hn hM
  · intro M₁ _ M₂ _ heq
    calc
      M₁ = transposeMatching n (transposeMatching n M₁) := (transposeMatching_invol n M₁).symm
      _ = transposeMatching n (transposeMatching n M₂) := by rw [heq]
      _ = M₂ := transposeMatching_invol n M₂
  · intro M' hM'
    exact ⟨transposeMatching n M', transpose_mem_FH_of_mem_FV hn hM', transposeMatching_invol n M'⟩

private theorem constructH_mem_FH {n : ℕ} (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val) :
    constructH n j₀ i_A i_B hle ∈ F_H n := by
  have hM := isDomiculeTiling_constructH j₀ i_A i_B hle
  have hdiagA : diagIdxA hM = (Finset.univ : Finset (Idx n)).erase (i_A, j₀) := by
    ext p
    simp [diagIdxA, mate_constructH, muH_embA_diagAdj_iff]
  have hcard : ((constructH n j₀ i_A i_B hle).filter (IsDiagDomicule n)).card = 2 * (n ^ 2 - 1) := by
    rw [filter_diag_card_eq_two_mul hM, hdiagA,
      Finset.card_erase_of_mem (Finset.mem_univ (i_A, j₀)), card_idx]
  simp only [F_H, subOneTilings, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨hM, hcard⟩, ?_⟩
  have heM : s(embA n (i_A, j₀), embC n (i_A, j₀)) ∈ constructH n j₀ i_A i_B hle := by
    rw [mk_mem_iff_mate hM, mate_constructH, muH_embA_apply]
    simp
  refine ⟨s(embA n (i_A, j₀), embC n (i_A, j₀)), heM, ?_⟩
  rw [isHorizDomino_mk]
  exact ⟨rfl, by simp [embA, embC, nat_dist_def]⟩

/-- Hardest lemma (`SCOPING-S017.md` §5.2, Steps 6–7): every horizontal-defect matching `M ∈ F_H n`
(`1 ≤ n`) collapses via nonnegative coordinate sums to a single strip `j₀ : Fin n` with
`i_A.val ≤ i_B.val` and equals `constructH n j₀ i_A i_B hle`. -/
theorem one_defect_strip_collapse_and_fiber_uniqueness {n : ℕ} (hn : 1 ≤ n)
    {M : Finset (Sym2 (Board n))} (hM_FH : M ∈ F_H n) :
    ∃ (j₀ i_A i_B : Fin n) (hle : i_A.val ≤ i_B.val),
      M = constructH n j₀ i_A i_B hle := by
  simp only [F_H, subOneTilings, Finset.mem_filter, Finset.mem_univ, true_and] at hM_FH
  rcases hM_FH with ⟨⟨hM, hcard⟩, hhoriz⟩
  obtain ⟨p_A, p_B, p_C, p_D, hpA, hpB, hpC, hpD, hdich⟩ := one_defect_dichotomy hn hM hcard
  rcases hdich with ⟨hAC, hBD, _⟩ | ⟨_, _, hno⟩
  · -- Step 6: Coordinate-sum strip collapse
    have hk_AC : kingAdj n (embA n p_A) (embC n p_C) := hAC ▸ kingAdj_mate hM (embA n p_A)
    have hk_BD : kingAdj n (embB n p_B) (embD n p_D) := hBD ▸ kingAdj_mate hM (embB n p_B)
    obtain ⟨hi_CA, hj_CA_lo, _⟩ := (kingAdj_embA_embC_iff p_A p_C).mp hk_AC
    obtain ⟨hi_DB, hj_BD_lo, _⟩ := (kingAdj_embB_embD_iff p_B p_D).mp hk_BD
    have hdiagA_mem : ∀ {p : Idx n}, p ≠ p_A → diagAdj n (embA n p) (mate hM (embA n p)) := by
      intro p hp
      by_contra hnd
      have hm : p ∈ orthIdxA hM := by simp [orthIdxA, hnd]
      rw [hpA, Finset.mem_singleton] at hm
      exact hp hm
    have hdiagC_mem : ∀ {p : Idx n}, p ≠ p_C → diagAdj n (embC n p) (mate hM (embC n p)) := by
      intro p hp
      by_contra hnd
      have hm : p ∈ orthIdxC hM := by simp [orthIdxC, hnd]
      rw [hpC, Finset.mem_singleton] at hm
      exact hp hm
    let φ : Idx n → Idx n := fun p => blk n (mate hM (embA n p))
    let ψ : Idx n → Idx n := fun p => blk n (mate hM (embC n p))
    have hφ_eq : ∀ {p : Idx n}, p ≠ p_A → mate hM (embA n p) = embB n (φ p) :=
      fun hp => diagAdj_embA_target (hdiagA_mem hp)
    have hψ_eq : ∀ {p : Idx n}, p ≠ p_C → mate hM (embC n p) = embD n (ψ p) :=
      fun hp => diagAdj_embC_target (hdiagC_mem hp)
    have hφ_maps : ∀ p ∈ (Finset.univ : Finset (Idx n)).erase p_A,
        φ p ∈ (Finset.univ : Finset (Idx n)).erase p_B := by
      intro p hp
      have hp_ne : p ≠ p_A := (Finset.mem_erase.mp hp).1
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hfeq
      have hm : mate hM (embA n p) = embB n p_B := by rw [hφ_eq hp_ne, hfeq]
      have hrev : mate hM (embB n p_B) = embA n p := by rw [← hm, mate_invol hM]
      rw [hBD] at hrev
      have hc := congrArg (fun x : Board n => x.1.val) hrev
      simp only [embD, embA] at hc
      omega
    have hψ_maps : ∀ p ∈ (Finset.univ : Finset (Idx n)).erase p_C,
        ψ p ∈ (Finset.univ : Finset (Idx n)).erase p_D := by
      intro p hp
      have hp_ne : p ≠ p_C := (Finset.mem_erase.mp hp).1
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hfeq
      have hm : mate hM (embC n p) = embD n p_D := by rw [hψ_eq hp_ne, hfeq]
      have hrev : mate hM (embD n p_D) = embC n p := by rw [← hm, mate_invol hM]
      have hDB : mate hM (embD n p_D) = embB n p_B := by rw [← hBD, mate_invol hM]
      rw [hDB] at hrev
      have hr := congrArg (fun x : Board n => x.1.val) hrev
      simp only [embB, embC] at hr
      omega
    have hφ_inj : Set.InjOn φ ((Finset.univ : Finset (Idx n)).erase p_A) := by
      intro p₁ hp₁ p₂ hp₂ heq
      have h1 : p₁ ≠ p_A := (Finset.mem_erase.mp hp₁).1
      have h2 : p₂ ≠ p_A := (Finset.mem_erase.mp hp₂).1
      have hm : mate hM (embA n p₁) = mate hM (embA n p₂) := by rw [hφ_eq h1, hφ_eq h2, heq]
      exact embA_injective n (mate_injective hM hm)
    have hψ_inj : Set.InjOn ψ ((Finset.univ : Finset (Idx n)).erase p_C) := by
      intro p₁ hp₁ p₂ hp₂ heq
      have h1 : p₁ ≠ p_C := (Finset.mem_erase.mp hp₁).1
      have h2 : p₂ ≠ p_C := (Finset.mem_erase.mp hp₂).1
      have hm : mate hM (embC n p₁) = mate hM (embC n p₂) := by rw [hψ_eq h1, hψ_eq h2, heq]
      exact embC_injective n (mate_injective hM hm)
    have hφ_bounds : ∀ p ∈ (Finset.univ : Finset (Idx n)).erase p_A,
        (φ p).1.val ≤ p.1.val ∧ p.1.val ≤ (φ p).1.val + 1 ∧
          (φ p).2.val ≤ p.2.val ∧ p.2.val ≤ (φ p).2.val + 1 := by
      intro p hp
      have hp_ne : p ≠ p_A := (Finset.mem_erase.mp hp).1
      have hd := hdiagA_mem hp_ne
      rwa [hφ_eq hp_ne, diagAdj_embA_embB_iff] at hd
    have hψ_bounds : ∀ p ∈ (Finset.univ : Finset (Idx n)).erase p_C,
        (ψ p).1.val ≤ p.1.val ∧ p.1.val ≤ (ψ p).1.val + 1 ∧
          p.2.val ≤ (ψ p).2.val ∧ (ψ p).2.val ≤ p.2.val + 1 := by
      intro p hp
      have hp_ne : p ≠ p_C := (Finset.mem_erase.mp hp).1
      have hd := hdiagC_mem hp_ne
      rwa [hψ_eq hp_ne, diagAdj_embC_embD_iff] at hd
    have hsum_jφ := punctured_bij_sum_diff (fun p : Idx n => p.2.val) hφ_maps hφ_inj
      (fun p hp => (hφ_bounds p hp).2.2.1)
    have hsum_jψ := punctured_bij_sum_diff_ge (fun p : Idx n => p.2.val) hψ_maps hψ_inj
      (fun p hp => (hψ_bounds p hp).2.2.1)
    have hsum_iφ := punctured_bij_sum_diff (fun p : Idx n => p.1.val) hφ_maps hφ_inj
      (fun p hp => (hφ_bounds p hp).1)
    set j₀ : Fin n := p_A.2
    set i_A : Fin n := p_A.1
    set i_B : Fin n := p_B.1
    have hjB_eq : p_B.2 = j₀ := Fin.ext (by omega)
    have hjC_eq : p_C.2 = j₀ := Fin.ext (by omega)
    have hjD_eq : p_D.2 = j₀ := Fin.ext (by omega)
    have hle : i_A.val ≤ i_B.val := by omega
    have hpA_pair : p_A = (i_A, j₀) := Prod.ext rfl rfl
    have hpB_pair : p_B = (i_B, j₀) := Prod.ext rfl hjB_eq
    have hpC_pair : p_C = (i_A, j₀) := Prod.ext hi_CA hjC_eq
    have hpD_pair : p_D = (i_B, j₀) := Prod.ext hi_DB hjD_eq
    have hjφ_zero : ∑ p ∈ (Finset.univ : Finset (Idx n)).erase p_A, (p.2.val - (φ p).2.val) = 0 := by
      have : p_B.2.val = p_A.2.val := congrArg Fin.val hjB_eq
      omega
    have hjψ_zero : ∑ p ∈ (Finset.univ : Finset (Idx n)).erase p_C, ((ψ p).2.val - p.2.val) = 0 := by
      have : p_D.2.val = p_C.2.val := by rw [hjD_eq, hjC_eq]
      omega
    have hjφ_all := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hjφ_zero
    have hjψ_all := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hjψ_zero
    have hφ_col : ∀ p ∈ (Finset.univ : Finset (Idx n)).erase (i_A, j₀), (φ p).2 = p.2 := by
      rw [← hpA_pair]
      intro p hp
      have h0 := hjφ_all p hp
      have h1 := (hφ_bounds p hp).2.2.1
      exact Fin.ext (by omega)
    have hψ_col : ∀ p ∈ (Finset.univ : Finset (Idx n)).erase (i_A, j₀), (ψ p).2 = p.2 := by
      rw [← hpC_pair]
      intro p hp
      have h0 := hjψ_all p hp
      have h1 := (hψ_bounds p hp).2.2.1
      exact Fin.ext (by omega)
    have hφ_uniq := punctured_strip_map_unique hle
      (hpA_pair ▸ hpB_pair ▸ hφ_maps)
      (hpA_pair ▸ hφ_inj)
      hφ_col
      (fun p hp => by
        have hb := hφ_bounds p (hpA_pair ▸ hp)
        exact ⟨hb.1, hb.2.1⟩)
    have hψ_uniq := punctured_strip_map_unique hle
      (hpC_pair ▸ hpD_pair ▸ hψ_maps)
      (hpC_pair ▸ hψ_inj)
      hψ_col
      (fun p hp => by
        have hb := hψ_bounds p (hpC_pair ▸ hp)
        exact ⟨hb.1, hb.2.1⟩)
    refine ⟨j₀, i_A, i_B, hle, ?_⟩
    have hmate_eq_A : ∀ p : Idx n, mate hM (embA n p) = muH j₀ i_A i_B hle (embA n p) := by
      intro p
      rw [muH_embA_apply]
      by_cases hp : p = (i_A, j₀)
      · simp only [hp, ↓reduceIte]
        calc
          mate hM (embA n (i_A, j₀)) = mate hM (embA n p_A) := by rw [hpA_pair]
          _ = embC n p_C := hAC
          _ = embC n (i_A, j₀) := by rw [hpC_pair]
      · simp only [hp, ↓reduceIte]
        have hp_ne : p ≠ p_A := by rwa [hpA_pair]
        have hp_mem : p ∈ (Finset.univ : Finset (Idx n)).erase (i_A, j₀) :=
          Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩
        rw [hφ_eq hp_ne, hφ_uniq p hp_mem]
        split_ifs <;> rfl
    have hmate_eq_C : ∀ p : Idx n, mate hM (embC n p) = muH j₀ i_A i_B hle (embC n p) := by
      intro p
      rw [muH_embC_apply]
      by_cases hp : p = (i_A, j₀)
      · simp only [hp, ↓reduceIte]
        calc
          mate hM (embC n (i_A, j₀)) = mate hM (embC n p_C) := by rw [hpC_pair]
          _ = mate hM (mate hM (embA n p_A)) := by rw [← hAC]
          _ = embA n p_A := mate_invol hM (embA n p_A)
          _ = embA n (i_A, j₀) := by rw [hpA_pair]
      · simp only [hp, ↓reduceIte]
        have hp_ne : p ≠ p_C := by rwa [hpC_pair]
        have hp_mem : p ∈ (Finset.univ : Finset (Idx n)).erase (i_A, j₀) :=
          Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩
        rw [hψ_eq hp_ne, hψ_uniq p hp_mem]
        split_ifs <;> rfl
    have hφ_surj : ((Finset.univ : Finset (Idx n)).erase p_A).image φ =
        (Finset.univ : Finset (Idx n)).erase p_B :=
      image_eq_of_injOn_of_card_eq hφ_maps hφ_inj (by simp [Finset.card_erase_of_mem])
    have hψ_surj : ((Finset.univ : Finset (Idx n)).erase p_C).image ψ =
        (Finset.univ : Finset (Idx n)).erase p_D :=
      image_eq_of_injOn_of_card_eq hψ_maps hψ_inj (by simp [Finset.card_erase_of_mem])
    have hmate_eq_B : ∀ q : Idx n, mate hM (embB n q) = muH j₀ i_A i_B hle (embB n q) := by
      intro q
      by_cases hq : q = p_B
      · subst q
        rw [hBD, hpB_pair, hpD_pair, muH_embB_defect]
      · have hq_mem : q ∈ (Finset.univ : Finset (Idx n)).erase p_B :=
          Finset.mem_erase.mpr ⟨hq, Finset.mem_univ q⟩
        rw [← hφ_surj, Finset.mem_image] at hq_mem
        rcases hq_mem with ⟨p, hp, rfl⟩
        have hp_ne : p ≠ p_A := (Finset.mem_erase.mp hp).1
        have h1 : embB n (φ p) = mate hM (embA n p) := (hφ_eq hp_ne).symm
        have h2 : embB n (φ p) = muH j₀ i_A i_B hle (embA n p) := h1.trans (hmate_eq_A p)
        calc
          mate hM (embB n (φ p)) = mate hM (mate hM (embA n p)) := by rw [h1]
          _ = embA n p := mate_invol hM (embA n p)
          _ = muH j₀ i_A i_B hle (muH j₀ i_A i_B hle (embA n p)) := (muH_invol j₀ i_A i_B hle _).symm
          _ = muH j₀ i_A i_B hle (embB n (φ p)) := by rw [← h2]
    have hmate_eq_D : ∀ q : Idx n, mate hM (embD n q) = muH j₀ i_A i_B hle (embD n q) := by
      intro q
      by_cases hq : q = p_D
      · subst q
        have hDB : mate hM (embD n p_D) = embB n p_B := by rw [← hBD, mate_invol hM]
        rw [hDB, hpD_pair, hpB_pair, ← muH_embB_defect j₀ i_A i_B hle, muH_invol]
      · have hq_mem : q ∈ (Finset.univ : Finset (Idx n)).erase p_D :=
          Finset.mem_erase.mpr ⟨hq, Finset.mem_univ q⟩
        rw [← hψ_surj, Finset.mem_image] at hq_mem
        rcases hq_mem with ⟨p, hp, rfl⟩
        have hp_ne : p ≠ p_C := (Finset.mem_erase.mp hp).1
        have h1 : embD n (ψ p) = mate hM (embC n p) := (hψ_eq hp_ne).symm
        have h2 : embD n (ψ p) = muH j₀ i_A i_B hle (embC n p) := h1.trans (hmate_eq_C p)
        calc
          mate hM (embD n (ψ p)) = mate hM (mate hM (embC n p)) := by rw [h1]
          _ = embC n p := mate_invol hM (embC n p)
          _ = muH j₀ i_A i_B hle (muH j₀ i_A i_B hle (embC n p)) := (muH_invol j₀ i_A i_B hle _).symm
          _ = muH j₀ i_A i_B hle (embD n (ψ p)) := by rw [← h2]
    apply tiling_ext_mate hM (isDomiculeTiling_constructH j₀ i_A i_B hle)
    intro v
    rw [mate_constructH]
    rcases board_four_cases v with hv | hv | hv | hv
    · rw [hv, hmate_eq_A]
    · rw [hv, hmate_eq_B]
    · rw [hv, hmate_eq_C]
    · rw [hv, hmate_eq_D]
  · exact absurd hhoriz hno

/-- Parameter set `{(j₀, i_A, i_B) : Fin n × (Fin n × Fin n) | i_A ≤ i_B}` for `F_H n`. -/
private def ParamH (n : ℕ) : Finset (Fin n × (Fin n × Fin n)) :=
  (Finset.univ : Finset (Fin n)) ×ˢ
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1.val ≤ p.2.val))

private theorem card_FH_eq_card_ParamH {n : ℕ} (hn : 1 ≤ n) :
    (F_H n).card = (ParamH n).card := by
  symm
  refine Finset.card_bij
    (fun q hq => constructH n q.1 q.2.1 q.2.2
      (by simp only [ParamH, Finset.mem_product, Finset.mem_filter] at hq; exact hq.2.2))
    ?_ ?_ ?_
  · intro q _
    exact constructH_mem_FH q.1 q.2.1 q.2.2 _
  · intro q₁ _ q₂ _ heq
    obtain ⟨hj, hiA, hiB⟩ := constructH_injective _ _ heq
    exact Prod.ext hj (Prod.ext hiA hiB)
  · intro M hM
    obtain ⟨j₀, i_A, i_B, hle, rfl⟩ := one_defect_strip_collapse_and_fiber_uniqueness hn hM
    refine ⟨(j₀, (i_A, i_B)), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩⟩

/-- Induction-free double-counting of upper-triangular pairs `{(i, j) : Fin n × Fin n | i ≤ j}`:
`2 * |U_le| = n * (n + 1)`. -/
private theorem two_mul_card_upperTri (n : ℕ) :
    2 * ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1.val ≤ p.2.val)).card =
      n * (n + 1) := by
  let U_le := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1.val ≤ p.2.val)
  let U_gt := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1.val ≤ p.2.val)
  let U_lt := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1.val < p.2.val)
  let Diag := (Finset.univ : Finset (Fin n)).image (fun i => (i, i))
  have htotal : U_le.card + U_gt.card = n * n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n × Fin n)))
      (fun p => p.1.val ≤ p.2.val)
    simpa [U_le, U_gt, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using this
  have hswap : U_lt.card = U_gt.card := by
    refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp
      simp only [U_lt, U_gt, Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap] at hp ⊢
      omega
    · intro p₁ _ p₂ _ heq
      exact Prod.swap_injective heq
    · intro q hq
      refine ⟨q.swap, ?_, Prod.swap_swap q⟩
      simp only [U_gt, U_lt, Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap] at hq ⊢
      omega
  have hsplit : U_le = Diag ∪ U_lt := by
    ext ⟨i, j⟩
    simp only [U_le, Diag, U_lt, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro hle
      rcases eq_or_lt_of_le hle with heq | hlt
      · left; exact ⟨i, rfl, Fin.ext heq⟩
      · right; exact hlt
    · rintro (⟨k, rfl, rfl⟩ | hlt)
      · exact le_rfl
      · exact le_of_lt hlt
  have hdisj : Disjoint Diag U_lt := by
    rw [Finset.disjoint_left]
    intro p hpD hpL
    rcases Finset.mem_image.mp hpD with ⟨i, _, rfl⟩
    simp only [U_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hpL
    omega
  have hcardD : Diag.card = n := by
    rw [Finset.card_image_of_injective _ (fun i j h => (Prod.mk.inj h).1),
      Finset.card_univ, Fintype.card_fin]
  have hcard_le : U_le.card = n + U_lt.card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj, hcardD]
  change 2 * U_le.card = n * (n + 1)
  have hlin : n + n * n = n * (n + 1) := by ring
  omega

end SubOne

/-- Dawid Ryłko's second conjecture on `OEIS A401673` (`%F` line 17):
for every `n ≥ 1`, `T(n, n^2 - 1) = A011379(n) = n^2 * (n + 1)`
(`2 * (n^2 - 1)` diagonal domicules). -/
theorem domiculeTilings_sub_one_diag_eq (n : ℕ) (hn : 1 ≤ n) :
    domiculeTilings n (n ^ 2 - 1) = n ^ 2 * (n + 1) := by
  rw [domiculeTilings_sub_one_eq_FH_add_FV, card_FV_eq_card_FH hn, ← two_mul,
    card_FH_eq_card_ParamH hn]
  unfold ParamH
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  calc
    2 * (n * ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1.val ≤ p.2.val)).card)
        = n * (2 * ((Finset.univ : Finset (Fin n × Fin n)).filter
            (fun p => p.1.val ≤ p.2.val)).card) := by ring
    _ = n * (n * (n + 1)) := by rw [two_mul_card_upperTri]
    _ = n ^ 2 * (n + 1) := by ring

/-! ### Section 7: Structural Corollaries, Boundary Witnesses, & Computable Mirror -/

/-- Companion reformulation directly in terms of `A011379`. -/
theorem domiculeTilings_sub_one_diag_eq_A011379 (n : ℕ) (hn : 1 ≤ n) :
    domiculeTilings n (n ^ 2 - 1) = A011379 n :=
  domiculeTilings_sub_one_diag_eq n hn

open scoped Classical in
/-- `OEIS A401673` `%C` line 11 parity law: in every domicule tiling `M` of the `2n × 2n` board,
the number of diagonal domicules is even. -/
theorem domicule_diag_card_even (n : ℕ) (M : Finset (Sym2 (Board n)))
    (hM : IsDomiculeTiling n M) :
    Even (M.filter (IsDiagDomicule n)).card := by
  rw [filter_diag_card_eq_two_mul hM]
  exact even_two_mul _

/-- `OEIS A401673` `%N` line 10 triangle support: `domiculeTilings n k = 0` whenever `n^2 < k`. -/
theorem domiculeTilings_eq_zero_of_gt (n k : ℕ) (hk : n ^ 2 < k) :
    domiculeTilings n k = 0 := by
  classical
  unfold domiculeTilings
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro M _
  rintro ⟨hM, hcard⟩
  have h1 := filter_diag_card_eq_two_mul hM
  have h2 := card_diag_add_orth_A hM
  omega

/-- Kernel witness that the `1 ≤ n` guard on Theorem 2 is mandatory under `ℕ` truncated subtraction
(`0^2 - 1 = 0`): `domiculeTilings 0 (0^2 - 1) = 1 ≠ 0 = A011379 0`. -/
theorem boundary_zero_guard_necessary :
    domiculeTilings 0 0 = 1 ∧
      domiculeTilings 0 (0 ^ 2 - 1) = 1 ∧
      A011379 0 = 0 ∧
      domiculeTilings 0 (0 ^ 2 - 1) ≠ A011379 0 := by
  have h0 : domiculeTilings 0 0 = 1 := domiculeTilings_max_diag_eq_one 0
  refine ⟨h0, h0, rfl, ?_⟩
  change domiculeTilings 0 0 ≠ 0
  rw [h0]
  decide

/-- Explicit `OEIS A401673` `%e` line 24 witness on the `2 × 2` board (`n = 1`):
the two crossing diagonal domicules `s((0, 0), (1, 1))` and `s((0, 1), (1, 0))` both belong to the
unique all-diagonal tiling `M_star 1` and are distinct diagonal domicules. -/
theorem crossing_diagonals_board1 :
    let d₁ : Sym2 (Board 1) := s((0, 0), (1, 1))
    let d₂ : Sym2 (Board 1) := s((0, 1), (1, 0))
    IsDomiculeTiling 1 (M_star 1) ∧
      d₁ ∈ M_star 1 ∧ d₂ ∈ M_star 1 ∧ d₁ ≠ d₂ ∧
      IsDiagDomicule 1 d₁ ∧ IsDiagDomicule 1 d₂ := by
  refine ⟨isDomiculeTiling_M_star 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(0, 0), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨(0, 1), Finset.mem_univ _, rfl⟩
  · intro heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1
  · rw [isDiagDomicule_mk]; exact ⟨rfl, rfl⟩
  · rw [isDiagDomicule_mk]; exact ⟨rfl, rfl⟩

/-- Explicit `n = 2` (`4 × 4` board) seam-shift witness (`j₀ = 0, i_A = 0, i_B = 1`):
`constructH 2 0 0 1` contains horizontal dominoes on top/bottom rows `0` and `3` together with the
seam-straddling X-cross `s((1, 0), (2, 1))` and `s((2, 0), (1, 1))` across rows `{1, 2}`. -/
theorem seam_shift_board2 :
    let M := constructH 2 0 0 1 (by decide)
    IsDomiculeTiling 2 M ∧
      (s((0, 0), (0, 1)) : Sym2 (Board 2)) ∈ M ∧
      (s((3, 0), (3, 1)) : Sym2 (Board 2)) ∈ M ∧
      (s((1, 0), (2, 1)) : Sym2 (Board 2)) ∈ M ∧
      (s((2, 0), (1, 1)) : Sym2 (Board 2)) ∈ M := by
  refine ⟨isDomiculeTiling_constructH 0 0 1 (by decide), ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(0, 0), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨(3, 0), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨(1, 0), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨(2, 0), Finset.mem_univ _, rfl⟩

/-- Kernel-proved spot checks on the literal pinned `domiculeTilings` and `A011379` across the
mandated boundary and interior values (`n = 0, 1, 2, 5, 6` and `A011379 (0..10)`). -/
theorem pinned_boundary_and_spot_checks :
    domiculeTilings 0 0 = 1 ∧
      domiculeTilings 1 1 = 1 ∧
      domiculeTilings 1 0 = 2 ∧
      domiculeTilings 2 4 = 1 ∧
      domiculeTilings 2 3 = 12 ∧
      domiculeTilings 5 25 = 1 ∧
      domiculeTilings 5 24 = 150 ∧
      domiculeTilings 6 36 = 1 ∧
      domiculeTilings 6 35 = 252 ∧
      (List.range 11).map A011379 = [0, 2, 12, 36, 80, 150, 252, 392, 576, 810, 1100] := by
  refine ⟨domiculeTilings_max_diag_eq_one 0,
    domiculeTilings_max_diag_eq_one 1,
    domiculeTilings_sub_one_diag_eq 1 (by decide),
    domiculeTilings_max_diag_eq_one 2,
    domiculeTilings_sub_one_diag_eq 2 (by decide),
    domiculeTilings_max_diag_eq_one 5,
    domiculeTilings_sub_one_diag_eq 5 (by decide),
    domiculeTilings_max_diag_eq_one 6,
    domiculeTilings_sub_one_diag_eq 6 (by decide),
    rfl⟩

/-- Constructively decidable mirror of `kingAdj`. -/
instance instDecidableKingAdj (n : ℕ) (u v : Board n) : Decidable (kingAdj n u v) :=
  inferInstanceAs (Decidable (u ≠ v ∧ Nat.dist u.1.val v.1.val ≤ 1 ∧ Nat.dist u.2.val v.2.val ≤ 1))

/-- Constructively decidable mirror of `diagAdj`. -/
instance instDecidableDiagAdj (n : ℕ) (u v : Board n) : Decidable (diagAdj n u v) :=
  inferInstanceAs (Decidable (Nat.dist u.1.val v.1.val = 1 ∧ Nat.dist u.2.val v.2.val = 1))

/-- Constructively decidable mirror of `IsDiagDomicule`. -/
instance instDecidableIsDiagDomicule (n : ℕ) (e : Sym2 (Board n)) : Decidable (IsDiagDomicule n e) :=
  inferInstanceAs (Decidable (∃ u v : Board n, e = s(u, v) ∧ diagAdj n u v))

/-- Constructively decidable mirror of `IsDomiculeTiling` replacing `∃! e` by `card = 1`. -/
def IsDomiculeTilingDec (n : ℕ) (M : Finset (Sym2 (Board n))) : Prop :=
  (∀ e ∈ M, ¬ e.IsDiag ∧ ∀ u v, e = s(u, v) → kingAdj n u v) ∧
    (∀ v : Board n, (M.filter (fun e => v ∈ e)).card = 1)

instance instDecidableIsDomiculeTilingDec (n : ℕ) (M : Finset (Sym2 (Board n))) :
    Decidable (IsDomiculeTilingDec n M) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Computable powerset mirror of `domiculeTilings` (evaluates directly on `n = 0, 1` without
`Classical.propDecidable`). -/
def domiculeTilingsDec (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Sym2 (Board n)))).filter (fun M =>
    IsDomiculeTilingDec n M ∧ (M.filter (IsDiagDomicule n)).card = 2 * k)).card

/-- Exact agreement `domiculeTilingsDec n k = domiculeTilings n k` for all `n, k : ℕ`. -/
theorem domiculeTilingsDec_eq (n k : ℕ) : domiculeTilingsDec n k = domiculeTilings n k := by
  unfold domiculeTilingsDec domiculeTilings
  apply congrArg Finset.card
  ext M
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr ?_ ?_
  · unfold IsDomiculeTilingDec IsDomiculeTiling
    refine and_congr Iff.rfl (forall_congr' fun v => ?_)
    rw [Finset.card_eq_one]
    constructor
    · rintro ⟨e, he⟩
      have hmem : e ∈ M.filter (fun e' => v ∈ e') := he ▸ Finset.mem_singleton_self e
      rw [Finset.mem_filter] at hmem
      refine ⟨e, hmem, fun e' he' => ?_⟩
      have hm' : e' ∈ M.filter (fun e'' => v ∈ e'') := Finset.mem_filter.mpr he'
      rwa [he, Finset.mem_singleton] at hm'
    · rintro ⟨e, he, huniq⟩
      refine ⟨e, ?_⟩
      ext e'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => huniq e' h, fun h => h ▸ he⟩
  · have hflt : ∀ (i₁ i₂ : DecidablePred (IsDiagDomicule n)),
        @Finset.filter _ (IsDiagDomicule n) i₁ M = @Finset.filter _ (IsDiagDomicule n) i₂ M :=
      fun i₁ i₂ => by rw [Subsingleton.elim i₁ i₂]
    rw [hflt (instDecidableIsDiagDomicule n) _]

/-- Direct kernel `rfl` check on the empty board `n = 0` via the proved-equivalent computable
mirror (`T(0, 0) = 1`, `T(0, 1) = 0`). -/
theorem kernel_rfl_board0 : domiculeTilingsDec 0 0 = 1 ∧ domiculeTilingsDec 0 1 = 0 :=
  ⟨rfl, rfl⟩

end SeamC.A401673
