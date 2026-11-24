import Mathlib.Data.Nat.Nth

/-!
# Seam B Entry C018 (OEIS A189640 1-Positions = A026232): Complete Lean 4 Proof

Proves both frozen theorems from `PIN-C018.md` v1
(`sha256: da0d52a6d4966c8908f92a046556ccf952b73d25139d9c66b5a81e5d18ba3a69`,
`Statement.lean sha256: cf8e092edee68db4fff56176b78927b04cfc70ba60e77d6f8b4af77ba6e0602d`):

1. `a026231_mod_three`: for all `n ≥ 1`, `a026231 n % 3 = 2` (exact division-by-3
   integrality of `A026232(n) = (A026231(n) + 1) / 3`).
2. `a189640_onePos_eq_a026232`: for all `n ≥ 1`, the `n`-th 1-based `1`-position
   of `A189640` equals `A026232(n)`.

Proof structure:
1. **Morphism fixed point (`A189640`):** Establish `(a189640Iter m).length = 3^m`,
   prefix stability, the 3-way ternary recurrence
   `a(1) = 0`, `a(3j + 1) = a(j + 1)`, `a(3j + 2) = 0`, `a(3j + 3) = 1`,
   and infinitude of `1`-positions.
2. **Uniform `lrState` persistence:** For any step offset `h` satisfying
   `GoodLR h` (`1 < R(n)`, `L(v) < R(n)`, strict monotonicity of `R`), prove
   no-overwrite persistence and exact extraction via `lrFill`.
3. **Residue classes of `A026142`:** Derive `a026142 (3r + 2) = 2r + 1`,
   `a026142 (3r + 1) = 6r + 2`, and `a026142 (3r) ∈ {2r, 6r}` for `r ≥ 1`.
4. **Complete residue-class characterization of `A026166` (resolving Dekking
   2020, §3):** Derive `a026166 (3r) = 6r - 2`, `a026166 (3r + 1) = 2r + 1`,
   and the branching recurrence `a026166_three_mul_add_two` for `r ≥ 1`.
5. **Ternary recurrence match & `Nat.nth` lift:** Prove
   `a026166 (t + 2) ≠ 2 * t + 2 ↔ a189640 (t + 1) = 1` by strong induction on `t`,
   deduce the set equivalence
   `(1 ≤ K ∧ a026166 K = a026142 K + 1) ↔ ∃ m, (1 ≤ m ∧ a189640 m = 1) ∧ K = 3 * m - 1`,
   and commute `Nat.nth` with `m ↦ 3 * m - 1` to close both pinned theorems.
-/

namespace MathProofs.SeamB.C018

/-! ### 0. Frozen Definitions (Verbatim from `PIN-C018.md` v1 / `Statement.lean`) -/

/-- Morphism `0 -> 001, 1 -> 101` on `{0, 1}` (`Fin 2`). -/
def a189640Morph : Fin 2 → List (Fin 2)
  | 0 => [0, 0, 1]
  | 1 => [1, 0, 1]

/-- `m`-th morphism iterate starting from seed `[0]` (length `3^m`). -/
def a189640Iter : ℕ → List (Fin 2)
  | 0 => [0]
  | m + 1 => (a189640Iter m).flatMap a189640Morph

/-- 1-based fixed-point sequence `A189640(n)` for `n ≥ 1` (`0` at `n = 0`). -/
def a189640 (n : ℕ) : ℕ :=
  if n = 0 then 0 else (((a189640Iter n)[n - 1]?).map Fin.val).getD 0

/-- 1-based `0`-position enumeration of `A189640` (companion C017). -/
noncomputable def a189640ZeroPos (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun k => 1 ≤ k ∧ a189640 k = 0) (n - 1)

/-- 1-based `1`-position enumeration of `A189640` (LHS of C018). -/
noncomputable def a189640OnePos (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun k => 1 ≤ k ∧ a189640 k = 1) (n - 1)

/-- Step-by-step partial array state of Kimberling's left-right filling algorithm
initialized at `a(1) = 1`. -/
def lrState (h : ℕ → ℕ) : ℕ → ℕ → Option ℕ
  | 0 => fun _ => none
  | 1 => fun k => if k = 1 then some 1 else none
  | m + 2 =>
    let st := lrState h (m + 1)
    let n := m + 2
    let d := h n
    let L := n - d
    let R := n + d
    let target := if (st L).isNone then L else R
    fun k => if k = target then some n else st k

/-- Total sequence reading the value assigned at index `k` at the earliest step
`m` where `k` becomes defined. -/
noncomputable def lrFill (h : ℕ → ℕ) (k : ℕ) : ℕ :=
  let m := sInf {m : ℕ | (lrState h m k).isSome}
  (lrState h m k).getD 0

/-- OEIS `A026166(k)` for `k ≥ 1` via `lrFill` with `h(n) = (n - 1) / 2`. -/
noncomputable def a026166 (k : ℕ) : ℕ :=
  lrFill (fun n => (n - 1) / 2) k

/-- OEIS `A026142(k)` for `k ≥ 1` via `lrFill` with `h(n) = (n + 1) / 2`. -/
noncomputable def a026142 (k : ℕ) : ℕ :=
  lrFill (fun n => (n + 1) / 2) k

/-- OEIS `A026231(n)`: 1-based `n`-th positive index `k ≥ 1` satisfying
`A026166(k) = A026142(k) + 1`. -/
noncomputable def a026231 (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun k => 1 ≤ k ∧ a026166 k = a026142 k + 1) (n - 1)

/-- OEIS `A026232(n) = (A026231(n) + 1) / 3` for `n ≥ 1` (RHS of C018). -/
noncomputable def a026232 (n : ℕ) : ℕ :=
  if n = 0 then 0 else (a026231 n + 1) / 3

/-! ### 1. Morphism Fixed Point `A189640` -/

private theorem fin2_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  rcases b with ⟨v, hv⟩
  match v, hv with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl

private theorem a189640Morph_length (b : Fin 2) : (a189640Morph b).length = 3 := by
  rcases fin2_cases b with rfl | rfl <;> rfl

private theorem flatMap_a189640Morph_length (l : List (Fin 2)) :
    (l.flatMap a189640Morph).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    simp [List.flatMap_cons, a189640Morph_length, ih]
    omega

theorem a189640Iter_length (m : ℕ) : (a189640Iter m).length = 3 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [a189640Iter, flatMap_a189640Morph_length, ih, Nat.pow_succ]
    omega

private theorem flatMap_a189640Morph_getElem? (l : List (Fin 2)) :
    ∀ j, j < l.length →
      (l.flatMap a189640Morph)[3 * j]? = l[j]? ∧
      (l.flatMap a189640Morph)[3 * j + 1]? = some 0 ∧
      (l.flatMap a189640Morph)[3 * j + 2]? = some 1 := by
  induction l with
  | nil =>
    intro j hj
    simp at hj
  | cons b t ih =>
    intro j hj
    cases j with
    | zero =>
      rcases fin2_cases b with rfl | rfl <;> simp [a189640Morph]
    | succ k =>
      have hk : k < t.length := by simpa using hj
      rcases ih k hk with ⟨h0, h1, h2⟩
      have e0 : 3 * (k + 1) = 3 * k + 3 := by omega
      have e1 : 3 * (k + 1) + 1 = (3 * k + 1) + 3 := by omega
      have e2 : 3 * (k + 1) + 2 = (3 * k + 2) + 3 := by omega
      rcases fin2_cases b with rfl | rfl
      · refine ⟨?_, ?_, ?_⟩
        · rw [e0]; simpa [a189640Morph] using h0
        · rw [e1]; simpa [a189640Morph] using h1
        · rw [e2]; simpa [a189640Morph] using h2
      · refine ⟨?_, ?_, ?_⟩
        · rw [e0]; simpa [a189640Morph] using h0
        · rw [e1]; simpa [a189640Morph] using h1
        · rw [e2]; simpa [a189640Morph] using h2

private theorem isPrefix_flatMap_a189640Morph {u v : List (Fin 2)} (h : u <+: v) :
    u.flatMap a189640Morph <+: v.flatMap a189640Morph := by
  rcases h with ⟨w, rfl⟩
  exact ⟨w.flatMap a189640Morph, by simp [List.flatMap_append]⟩

private theorem a189640Iter_isPrefix_succ (m : ℕ) :
    a189640Iter m <+: a189640Iter (m + 1) := by
  induction m with
  | zero => exact ⟨[0, 1], rfl⟩
  | succ m ih => exact isPrefix_flatMap_a189640Morph ih

private theorem a189640Iter_isPrefix_of_le {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    a189640Iter m₁ <+: a189640Iter m₂ := by
  induction m₂, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k _ ih => exact ih.trans (a189640Iter_isPrefix_succ k)

private theorem lt_three_pow (n : ℕ) : n < 3 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

private theorem a189640Iter_getElem?_of_le {m₁ m₂ j : ℕ} (hle : m₁ ≤ m₂) (hj : j < 3 ^ m₁) :
    (a189640Iter m₁)[j]? = (a189640Iter m₂)[j]? := by
  rcases a189640Iter_isPrefix_of_le hle with ⟨w, hw⟩
  rw [← hw, List.getElem?_append_left]
  rw [a189640Iter_length]
  exact hj

private theorem a189640Iter_getElem?_stable {m j : ℕ} (hj : j < 3 ^ m) :
    (a189640Iter m)[j]? = (a189640Iter (j + 1))[j]? := by
  rcases le_total m (j + 1) with hle | hle
  · exact a189640Iter_getElem?_of_le hle hj
  · have hj' : j < 3 ^ (j + 1) := lt_trans (Nat.lt_succ_self j) (lt_three_pow (j + 1))
    exact (a189640Iter_getElem?_of_le hle hj').symm

theorem a189640_one : a189640 1 = 0 := rfl

theorem a189640_three_mul_add_one (j : ℕ) : a189640 (3 * j + 1) = a189640 (j + 1) := by
  have hj : j < 3 ^ (j + 1) := lt_trans (Nat.lt_succ_self j) (lt_three_pow (j + 1))
  have h3j : 3 * j < 3 ^ (j + 2) := by
    rw [Nat.pow_succ]
    omega
  have hlen : j < (a189640Iter (j + 1)).length := by
    rw [a189640Iter_length]
    exact hj
  have hget : (a189640Iter (3 * j + 1))[3 * j]? = (a189640Iter (j + 1))[j]? := by
    rw [← a189640Iter_getElem?_stable h3j]
    exact (flatMap_a189640Morph_getElem? (a189640Iter (j + 1)) j hlen).1
  simp only [a189640, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, hget]

theorem a189640_three_mul_add_two (j : ℕ) : a189640 (3 * j + 2) = 0 := by
  have hj : j < 3 ^ (j + 1) := lt_trans (Nat.lt_succ_self j) (lt_three_pow (j + 1))
  have h3j : 3 * j + 1 < 3 ^ (j + 2) := by
    rw [Nat.pow_succ]
    omega
  have hlen : j < (a189640Iter (j + 1)).length := by
    rw [a189640Iter_length]
    exact hj
  have hget : (a189640Iter (3 * j + 2))[3 * j + 1]? = some 0 := by
    rw [← a189640Iter_getElem?_stable h3j]
    exact (flatMap_a189640Morph_getElem? (a189640Iter (j + 1)) j hlen).2.1
  have hsub : 3 * j + 2 - 1 = 3 * j + 1 := by omega
  simp [a189640, hsub, hget]

theorem a189640_three_mul_add_three (j : ℕ) : a189640 (3 * j + 3) = 1 := by
  have hj : j < 3 ^ (j + 1) := lt_trans (Nat.lt_succ_self j) (lt_three_pow (j + 1))
  have h3j : 3 * j + 2 < 3 ^ (j + 2) := by
    rw [Nat.pow_succ]
    omega
  have hlen : j < (a189640Iter (j + 1)).length := by
    rw [a189640Iter_length]
    exact hj
  have hget : (a189640Iter (3 * j + 3))[3 * j + 2]? = some 1 := by
    rw [← a189640Iter_getElem?_stable h3j]
    exact (flatMap_a189640Morph_getElem? (a189640Iter (j + 1)) j hlen).2.2
  have hsub : 3 * j + 3 - 1 = 3 * j + 2 := by omega
  simp [a189640, hsub, hget]

private theorem a189640_one_infinite :
    Set.Infinite {k : ℕ | 1 ≤ k ∧ a189640 k = 1} := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  refine ⟨3 * n + 3, ⟨by omega, a189640_three_mul_add_three n⟩, by omega⟩

/-! ### 2. Uniform `lrState` Persistence and `lrFill` Extraction -/

/-- Arithmetic regularity conditions on the left-right step offset `h` guaranteeing
that no array cell is ever overwritten during `lrState h`. -/
private structure GoodLR (h : ℕ → ℕ) : Prop where
  r_gt_one : ∀ n, 2 ≤ n → 1 < n + h n
  l_lt_r : ∀ v n, 2 ≤ v → v < n → v - h v < n + h n
  r_strictMono : ∀ v n, 2 ≤ v → v < n → v + h v < n + h n

private theorem lrState_step (h : ℕ → ℕ) (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    lrState h n k =
      let st := lrState h (n - 1)
      let d := h n
      let L := n - d
      let R := n + d
      let target := if (st L).isNone then L else R
      if k = target then some n else st k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rfl

private theorem lrState_some_spec (h : ℕ → ℕ) :
    ∀ m k v, lrState h m k = some v →
      (k = 1 ∧ v = 1 ∧ 1 ≤ m) ∨
      (2 ≤ v ∧ v ≤ m ∧ (k = v - h v ∨ k = v + h v)) := by
  intro m
  induction m with
  | zero =>
    intro k v hst
    simp [lrState] at hst
  | succ m ih =>
    cases m with
    | zero =>
      intro k v hst
      by_cases hk : k = 1
      · simp only [lrState, hk, ↓reduceIte] at hst
        exact Or.inl ⟨hk, (Option.some.inj hst).symm, le_rfl⟩
      · simp [lrState, hk] at hst
    | succ m =>
      intro k v hst
      rw [lrState_step h (m + 2) (by omega) k] at hst
      dsimp only at hst
      set target :=
        if (lrState h (m + 2 - 1) (m + 2 - h (m + 2))).isNone
        then m + 2 - h (m + 2) else m + 2 + h (m + 2)
      by_cases hkt : k = target
      · simp only [hkt, ↓reduceIte] at hst
        right
        have hv : m + 2 = v := Option.some.inj hst
        subst hv
        refine ⟨by omega, by omega, ?_⟩
        dsimp only [target] at hkt
        by_cases hL : (lrState h (m + 2 - 1) (m + 2 - h (m + 2))).isNone = true
        · simp only [hL, ↓reduceIte] at hkt
          exact Or.inl hkt
        · simp only [hL] at hkt
          exact Or.inr hkt
      · simp only [hkt, ↓reduceIte] at hst
        have hst' : lrState h (m + 1) k = some v := hst
        rcases ih k v hst' with ⟨hk1, hv1, hm1⟩ | ⟨hv2, hvm, hpos⟩
        · exact Or.inl ⟨hk1, hv1, by omega⟩
        · exact Or.inr ⟨hv2, by omega, hpos⟩

private theorem lrState_some_le {h : ℕ → ℕ} {m k v : ℕ} (hst : lrState h m k = some v) :
    v ≤ m := by
  rcases lrState_some_spec h m k v hst with ⟨_, hv1, hm1⟩ | ⟨_, hvm, _⟩ <;> omega

private theorem lrState_target_none {h : ℕ → ℕ} (hg : GoodLR h) (n : ℕ) (hn : 2 ≤ n) :
    let st := lrState h (n - 1)
    let L := n - h n
    let R := n + h n
    let target := if (st L).isNone then L else R
    st target = none := by
  dsimp only
  split_ifs with hL
  · exact Option.isNone_iff_eq_none.mp hL
  · cases hR : lrState h (n - 1) (n + h n) with
    | none => rfl
    | some v =>
      rcases lrState_some_spec h (n - 1) (n + h n) v hR with ⟨h1, _, _⟩ | ⟨hv2, hvn, hpos⟩
      · have := hg.r_gt_one n hn
        omega
      · rcases hpos with hL' | hR'
        · have := hg.l_lt_r v n hv2 (by omega)
          omega
        · have := hg.r_strictMono v n hv2 (by omega)
          omega

private theorem lrState_mono {h : ℕ → ℕ} (hg : GoodLR h) {m₁ m₂ k v : ℕ}
    (hle : m₁ ≤ m₂) (hst : lrState h m₁ k = some v) :
    lrState h m₂ k = some v := by
  induction m₂, hle using Nat.le_induction with
  | base => exact hst
  | succ m hm ih =>
    cases m with
    | zero =>
      have hm1 : m₁ = 0 := by omega
      subst hm1
      simp [lrState] at hst
    | succ m =>
      rw [lrState_step h (m + 2) (by omega) k]
      dsimp only
      have htn := lrState_target_none hg (m + 2) (by omega)
      dsimp only at htn
      set target :=
        if (lrState h (m + 2 - 1) (m + 2 - h (m + 2))).isNone
        then m + 2 - h (m + 2) else m + 2 + h (m + 2)
      by_cases hkt : k = target
      · exfalso
        have hnone : lrState h (m + 1) k = none := by
          rw [hkt]
          exact htn
        rw [hnone] at ih
        simp at ih
      · simp only [hkt, ↓reduceIte]
        exact ih

private theorem lrState_unique {h : ℕ → ℕ} (hg : GoodLR h) {m₁ m₂ k v₁ v₂ : ℕ}
    (h1 : lrState h m₁ k = some v₁) (h2 : lrState h m₂ k = some v₂) :
    v₁ = v₂ := by
  rcases le_total m₁ m₂ with hle | hle
  · have h1' := lrState_mono hg hle h1
    rw [h1'] at h2
    exact Option.some.inj h2
  · have h2' := lrState_mono hg hle h2
    rw [h2'] at h1
    exact (Option.some.inj h1).symm

private theorem lrFill_eq_of_lrState {h : ℕ → ℕ} (hg : GoodLR h) {m k v : ℕ}
    (hst : lrState h m k = some v) :
    lrFill h k = v := by
  unfold lrFill
  dsimp only
  set S : Set ℕ := {m' : ℕ | (lrState h m' k).isSome}
  have hS : S.Nonempty := ⟨m, by simp [S, hst]⟩
  have hmem : (lrState h (sInf S) k).isSome := Nat.sInf_mem hS
  rcases Option.isSome_iff_exists.mp hmem with ⟨w, hw⟩
  have hvw : w = v := lrState_unique hg hw hst
  rw [hw, hvw]
  rfl

private theorem lrState_none_of_no_writer (h : ℕ → ℕ) (m k : ℕ)
    (hk1 : k ≠ 1) (hno : ∀ v, 2 ≤ v → v ≤ m → k ≠ v - h v ∧ k ≠ v + h v) :
    lrState h m k = none := by
  cases hst : lrState h m k with
  | none => rfl
  | some v =>
    rcases lrState_some_spec h m k v hst with ⟨h1, _, _⟩ | ⟨hv2, hvm, hpos⟩
    · exact (hk1 h1).elim
    · rcases hno v hv2 hvm with ⟨hL, hR⟩
      rcases hpos with hL' | hR'
      · exact (hL hL').elim
      · exact (hR hR').elim

private theorem lrState_none_preserve (h : ℕ → ℕ) {m₁ m₂ k : ℕ} (hle : m₁ ≤ m₂)
    (h1 : 1 ≤ m₁) (hnone : lrState h m₁ k = none)
    (hno : ∀ v, m₁ < v → v ≤ m₂ → k ≠ v - h v ∧ k ≠ v + h v) :
    lrState h m₂ k = none := by
  induction m₂, hle using Nat.le_induction with
  | base => exact hnone
  | succ m hm ih =>
    have hm2 : 2 ≤ m + 1 := by omega
    have hprev : lrState h m k = none :=
      ih (fun v hv1 hv2 => hno v hv1 (by omega))
    rw [lrState_step h (m + 1) hm2 k]
    dsimp only
    rcases hno (m + 1) (by omega) le_rfl with ⟨hL, hR⟩
    have hkt : k ≠ if (lrState h (m + 1 - 1) (m + 1 - h (m + 1))).isNone
        then m + 1 - h (m + 1) else m + 1 + h (m + 1) := by
      split_ifs <;> assumption
    simp only [hkt, ↓reduceIte]
    simpa using hprev

private theorem lrState_write_L (h : ℕ → ℕ) {n k : ℕ} (hn : 2 ≤ n)
    (hk : k = n - h n) (hnone : lrState h (n - 1) k = none) :
    lrState h n k = some n := by
  rw [lrState_step h n hn k]
  dsimp only
  subst hk
  simp [hnone]

private theorem lrState_write_R (h : ℕ → ℕ) {n k : ℕ} (hn : 2 ≤ n)
    (hk : k = n + h n) (hsome : (lrState h (n - 1) (n - h n)).isSome) :
    lrState h n k = some n := by
  rw [lrState_step h n hn k]
  dsimp only
  have hnotnone : (lrState h (n - 1) (n - h n)).isNone = false := by
    cases hst : lrState h (n - 1) (n - h n) with
    | none => simp [hst] at hsome
    | some _ => rfl
  simp [hnotnone, hk]

private theorem lrState_isSome_after_L {h : ℕ → ℕ} (hg : GoodLR h) {n k : ℕ}
    (hn : 2 ≤ n) (hk : k = n - h n) :
    (lrState h n k).isSome := by
  cases hprev : lrState h (n - 1) k with
  | none =>
    rw [lrState_write_L h hn hk hprev]
    rfl
  | some v =>
    rw [lrState_mono hg (by omega : n - 1 ≤ n) hprev]
    rfl

/-! ### 3. Residue Classes of `A026142` -/

private def h42 (n : ℕ) : ℕ := (n + 1) / 2

private theorem goodLR_h42 : GoodLR h42 where
  r_gt_one n hn := by simp only [h42]; omega
  l_lt_r v n hv hvn := by simp only [h42]; omega
  r_strictMono v n hv hvn := by simp only [h42]; omega

theorem a026142_one : a026142 1 = 1 :=
  lrFill_eq_of_lrState goodLR_h42 (m := 1) rfl

theorem a026142_two : a026142 2 = 4 :=
  lrFill_eq_of_lrState goodLR_h42 (m := 4) rfl

theorem a026142_three : a026142 3 = 2 :=
  lrFill_eq_of_lrState goodLR_h42 (m := 2) rfl

theorem a026142_four : a026142 4 = 8 :=
  lrFill_eq_of_lrState goodLR_h42 (m := 8) rfl

theorem a026142_three_mul_add_two (r : ℕ) (hr : 1 ≤ r) :
    a026142 (3 * r + 2) = 2 * r + 1 := by
  have hocc : (lrState h42 (2 * r) r).isSome :=
    lrState_isSome_after_L goodLR_h42 (n := 2 * r) (by omega) (by simp only [h42]; omega)
  have hwrite : lrState h42 (2 * r + 1) (3 * r + 2) = some (2 * r + 1) :=
    lrState_write_R h42 (n := 2 * r + 1) (by omega) (by simp only [h42]; omega) (by
      have hL : 2 * r + 1 - h42 (2 * r + 1) = r := by simp only [h42]; omega
      have hsub : 2 * r + 1 - 1 = 2 * r := by omega
      rw [hL, hsub]
      exact hocc)
  exact lrFill_eq_of_lrState goodLR_h42 hwrite

theorem a026142_three_mul_add_one (r : ℕ) (hr : 1 ≤ r) :
    a026142 (3 * r + 1) = 6 * r + 2 := by
  have hnone : lrState h42 (6 * r + 1) (3 * r + 1) = none :=
    lrState_none_of_no_writer h42 (6 * r + 1) (3 * r + 1) (by omega) (by
      intro v hv2 hvm
      simp only [h42]
      constructor <;> omega)
  have hwrite : lrState h42 (6 * r + 2) (3 * r + 1) = some (6 * r + 2) :=
    lrState_write_L h42 (n := 6 * r + 2) (by omega) (by simp only [h42]; omega) (by
      have hsub : 6 * r + 2 - 1 = 6 * r + 1 := by omega
      rw [hsub]
      exact hnone)
  exact lrFill_eq_of_lrState goodLR_h42 hwrite

theorem a026142_three_mul_cases (r : ℕ) (hr : 1 ≤ r) :
    a026142 (3 * r) = 2 * r ∨ a026142 (3 * r) = 6 * r := by
  cases hst : lrState h42 (6 * r - 1) (3 * r) with
  | some v =>
    left
    rcases lrState_some_spec h42 (6 * r - 1) (3 * r) v hst with ⟨h1, _, _⟩ | ⟨hv2, hvm, hpos⟩
    · omega
    · have hv : v = 2 * r := by
        simp only [h42] at hpos
        omega
      rw [← hv]
      exact lrFill_eq_of_lrState goodLR_h42 hst
  | none =>
    right
    have hwrite : lrState h42 (6 * r) (3 * r) = some (6 * r) :=
      lrState_write_L h42 (n := 6 * r) (by omega) (by simp only [h42]; omega) hst
    exact lrFill_eq_of_lrState goodLR_h42 hwrite

/-! ### 4. Complete Residue-Class Characterization of `A026166` (Resolving Dekking 2020 §3) -/

private def h66 (n : ℕ) : ℕ := (n - 1) / 2

private theorem goodLR_h66 : GoodLR h66 where
  r_gt_one n hn := by simp only [h66]; omega
  l_lt_r v n hv hvn := by simp only [h66]; omega
  r_strictMono v n hv hvn := by simp only [h66]; omega

theorem a026166_one : a026166 1 = 1 :=
  lrFill_eq_of_lrState goodLR_h66 (m := 1) rfl

theorem a026166_two : a026166 2 = 2 :=
  lrFill_eq_of_lrState goodLR_h66 (m := 2) rfl

theorem a026166_three : a026166 3 = 4 :=
  lrFill_eq_of_lrState goodLR_h66 (m := 4) rfl

theorem a026166_four : a026166 4 = 3 :=
  lrFill_eq_of_lrState goodLR_h66 (m := 3) rfl

theorem a026166_three_mul (r : ℕ) (hr : 1 ≤ r) :
    a026166 (3 * r) = 6 * r - 2 := by
  have hnone : lrState h66 (6 * r - 3) (3 * r) = none :=
    lrState_none_of_no_writer h66 (6 * r - 3) (3 * r) (by omega) (by
      intro v hv2 hvm
      simp only [h66]
      constructor <;> omega)
  have hwrite : lrState h66 (6 * r - 2) (3 * r) = some (6 * r - 2) :=
    lrState_write_L h66 (n := 6 * r - 2) (by omega) (by simp only [h66]; omega) (by
      have hsub : 6 * r - 2 - 1 = 6 * r - 3 := by omega
      rw [hsub]
      exact hnone)
  exact lrFill_eq_of_lrState goodLR_h66 hwrite

theorem a026166_three_mul_add_one (r : ℕ) (hr : 1 ≤ r) :
    a026166 (3 * r + 1) = 2 * r + 1 := by
  have hocc : (lrState h66 (2 * r) (r + 1)).isSome :=
    lrState_isSome_after_L goodLR_h66 (n := 2 * r) (by omega) (by simp only [h66]; omega)
  have hwrite : lrState h66 (2 * r + 1) (3 * r + 1) = some (2 * r + 1) :=
    lrState_write_R h66 (n := 2 * r + 1) (by omega) (by simp only [h66]; omega) (by
      have hL : 2 * r + 1 - h66 (2 * r + 1) = r + 1 := by simp only [h66]; omega
      have hsub : 2 * r + 1 - 1 = 2 * r := by omega
      rw [hL, hsub]
      exact hocc)
  exact lrFill_eq_of_lrState goodLR_h66 hwrite

/-- Complete branching recurrence for `A026166(3r + 2)` (`r ≥ 1`), resolving the
characterization of `A026166` left to the reader in Dekking (2020, §3). -/
theorem a026166_three_mul_add_two (r : ℕ) (hr : 1 ≤ r) :
    a026166 (3 * r + 2) =
      if a026166 (r + 2) = 2 * r + 2 then 6 * r + 2 else 2 * r + 2 := by
  cases hcell : lrState h66 (2 * r + 1) (r + 2) with
  | none =>
    have hL2 : 2 * r + 2 - h66 (2 * r + 2) = r + 2 := by simp only [h66]; omega
    have hsub2 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
    have hwriteL : lrState h66 (2 * r + 2) (r + 2) = some (2 * r + 2) :=
      lrState_write_L h66 (n := 2 * r + 2) (by omega) hL2.symm (by rw [hsub2]; exact hcell)
    have ha_r2 : a026166 (r + 2) = 2 * r + 2 :=
      lrFill_eq_of_lrState goodLR_h66 hwriteL
    simp only [ha_r2, ↓reduceIte]
    have hnone_before : lrState h66 (2 * r + 1) (3 * r + 2) = none :=
      lrState_none_of_no_writer h66 (2 * r + 1) (3 * r + 2) (by omega) (by
        intro v hv2 hvm
        simp only [h66]
        constructor <;> omega)
    have hnone_at : lrState h66 (2 * r + 2) (3 * r + 2) = none := by
      rw [lrState_step h66 (2 * r + 2) (by omega) (3 * r + 2)]
      dsimp only
      rw [hsub2, hL2, hcell]
      have hne : 3 * r + 2 ≠ r + 2 := by omega
      simp only [Option.isNone_none, ↓reduceIte, hne]
      exact hnone_before
    have hnone_after : lrState h66 (6 * r + 1) (3 * r + 2) = none :=
      lrState_none_preserve h66 (by omega : 2 * r + 2 ≤ 6 * r + 1) (by omega) hnone_at (by
        intro v hv1 hv2
        simp only [h66]
        constructor <;> omega)
    have hwrite6 : lrState h66 (6 * r + 2) (3 * r + 2) = some (6 * r + 2) :=
      lrState_write_L h66 (n := 6 * r + 2) (by omega) (by simp only [h66]; omega) (by
        have hsub6 : 6 * r + 2 - 1 = 6 * r + 1 := by omega
        rw [hsub6]
        exact hnone_after)
    exact lrFill_eq_of_lrState goodLR_h66 hwrite6
  | some v =>
    have hv_le : v ≤ 2 * r + 1 := lrState_some_le hcell
    have ha_r2 : a026166 (r + 2) = v := lrFill_eq_of_lrState goodLR_h66 hcell
    have hne : a026166 (r + 2) ≠ 2 * r + 2 := by omega
    simp only [hne, ↓reduceIte]
    have hwriteR : lrState h66 (2 * r + 2) (3 * r + 2) = some (2 * r + 2) :=
      lrState_write_R h66 (n := 2 * r + 2) (by omega) (by simp only [h66]; omega) (by
        have hL2 : 2 * r + 2 - h66 (2 * r + 2) = r + 2 := by simp only [h66]; omega
        have hsub2 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
        rw [hL2, hsub2, hcell]
        rfl)
    exact lrFill_eq_of_lrState goodLR_h66 hwriteR

/-! ### 5. Ternary Recurrence Match, Set Equivalence, and `Nat.nth` Lift -/

/-- Exact coincidence of the `A026166` branching predicate with the fixed point
`A189640`: `A026166(t + 2) ≠ 2t + 2` iff `A189640(t + 1) = 1`, for all `t : ℕ`. -/
theorem a026166_ne_two_mul_iff_a189640 (t : ℕ) :
    a026166 (t + 2) ≠ 2 * t + 2 ↔ a189640 (t + 1) = 1 := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases ht0 : t = 0
    · subst ht0
      simp [a026166_two, a189640_one]
    · set u := t / 3
      have hdiv : t = 3 * u + t % 3 := by omega
      have hmod : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
      rcases hmod with hm0 | hm1 | hm2
      · have htu : t = 3 * u := by omega
        have hu1 : 1 ≤ u := by omega
        have hult : u < t := by omega
        rw [htu, a189640_three_mul_add_one u, a026166_three_mul_add_two u hu1]
        have hih := ih u hult
        split_ifs with hcond
        · constructor
          · intro hne
            omega
          · intro h1
            exact (hih.mpr h1 hcond).elim
        · constructor
          · intro _
            exact hih.mp hcond
          · intro _
            omega
      · have htu : t = 3 * u + 1 := by omega
        rw [htu, a189640_three_mul_add_two u]
        have hidx : 3 * u + 1 + 2 = 3 * (u + 1) := by omega
        rw [hidx, a026166_three_mul (u + 1) (by omega)]
        constructor <;> omega
      · have htu : t = 3 * u + 2 := by omega
        rw [htu, a189640_three_mul_add_three u]
        have hidx : 3 * u + 2 + 2 = 3 * (u + 1) + 1 := by omega
        rw [hidx, a026166_three_mul_add_one (u + 1) (by omega)]
        constructor <;> omega

/-- Exact set-level equivalence characterizing `A026231`:
`K ≥ 1 ∧ A026166(K) = A026142(K) + 1` iff `K = 3m - 1` for some `m ≥ 1` with `A189640(m) = 1`. -/
theorem a026231_pred_iff (K : ℕ) :
    (1 ≤ K ∧ a026166 K = a026142 K + 1) ↔
      ∃ m : ℕ, (1 ≤ m ∧ a189640 m = 1) ∧ K = 3 * m - 1 := by
  constructor
  · rintro ⟨hK1, heq⟩
    by_cases hsmall : K ≤ 4
    · have : K = 1 ∨ K = 2 ∨ K = 3 ∨ K = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · simp [a026166_one, a026142_one] at heq
      · simp [a026166_two, a026142_two] at heq
      · simp [a026166_three, a026142_three] at heq
      · simp [a026166_four, a026142_four] at heq
    · set r := K / 3
      have hmod : K % 3 = 0 ∨ K % 3 = 1 ∨ K % 3 = 2 := by omega
      rcases hmod with hm0 | hm1 | hm2
      · have hKr : K = 3 * r := by omega
        have hr1 : 1 ≤ r := by omega
        rw [hKr, a026166_three_mul r hr1] at heq
        rcases a026142_three_mul_cases r hr1 with h | h <;> rw [h] at heq <;> omega
      · have hKr : K = 3 * r + 1 := by omega
        have hr1 : 1 ≤ r := by omega
        rw [hKr, a026166_three_mul_add_one r hr1, a026142_three_mul_add_one r hr1] at heq
        omega
      · have hKr : K = 3 * r + 2 := by omega
        have hr1 : 1 ≤ r := by omega
        rw [hKr, a026142_three_mul_add_two r hr1, a026166_three_mul_add_two r hr1] at heq
        have hne : a026166 (r + 2) ≠ 2 * r + 2 := by
          intro hcond
          simp only [hcond, ↓reduceIte] at heq
          omega
        have ha1 : a189640 (r + 1) = 1 := (a026166_ne_two_mul_iff_a189640 r).mp hne
        exact ⟨r + 1, ⟨by omega, ha1⟩, by omega⟩
  · rintro ⟨m, ⟨hm1, ha1⟩, rfl⟩
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have hm_eq : m = 1 := by omega
      subst hm_eq
      simp [a189640_one] at ha1
    set r := m - 1
    have hmr : m = r + 1 := by omega
    have hr1 : 1 ≤ r := by omega
    have hK : 3 * m - 1 = 3 * r + 2 := by omega
    rw [hK]
    refine ⟨by omega, ?_⟩
    rw [a026142_three_mul_add_two r hr1, a026166_three_mul_add_two r hr1]
    have hne : a026166 (r + 2) ≠ 2 * r + 2 :=
      (a026166_ne_two_mul_iff_a189640 r).mpr (by rw [← hmr]; exact ha1)
    simp only [hne, ↓reduceIte]

/-- Two strictly monotone functions `ℕ → ℕ` with the same image are equal. -/
private theorem strictMono_eq_of_same_range {f g : ℕ → ℕ}
    (hf : StrictMono f) (hg : StrictMono g)
    (hfg : ∀ i, ∃ j, g j = f i) (hgf : ∀ i, ∃ j, f j = g i) :
    ∀ i, f i = g i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    have hle1 : f i ≤ g i := by
      rcases hgf i with ⟨a, ha⟩
      by_cases hai : a < i
      · have hfa : f a = g a := ih a hai
        have hlt : g a < g i := hg hai
        omega
      · have hia : i ≤ a := by omega
        calc f i ≤ f a := hf.monotone hia
          _ = g i := ha
    have hle2 : g i ≤ f i := by
      rcases hfg i with ⟨b, hb⟩
      by_cases hbi : b < i
      · have hfb : f b = g b := ih b hbi
        have hlt : f b < f i := hf hbi
        omega
      · have hib : i ≤ b := by omega
        calc g i ≤ g b := hg.monotone hib
          _ = f i := hb
    omega

/-- Commutation of `Nat.nth` with the strictly monotone affine map `m ↦ 3 * m - 1`
on subsets of `ℕ_{≥ 1}`. -/
private theorem nth_three_mul_sub_one {P Q : ℕ → Prop}
    (hPinf : Set.Infinite {m : ℕ | P m})
    (hPpos : ∀ m, P m → 1 ≤ m)
    (hQ : ∀ K, Q K ↔ ∃ m, P m ∧ K = 3 * m - 1) :
    ∀ i, Nat.nth Q i = 3 * Nat.nth P i - 1 := by
  classical
  have hQinf : Set.Infinite {K : ℕ | Q K} := by
    apply Set.infinite_of_forall_exists_gt
    intro n
    rcases hPinf.exists_gt n with ⟨m, hmP, hmn⟩
    have hm1 : 1 ≤ m := hPpos m hmP
    refine ⟨3 * m - 1, (hQ (3 * m - 1)).mpr ⟨m, hmP, rfl⟩, by omega⟩
  let f : ℕ → ℕ := fun i => Nat.nth Q i
  let g : ℕ → ℕ := fun i => 3 * Nat.nth P i - 1
  have hf : StrictMono f := Nat.nth_strictMono hQinf
  have hg : StrictMono g := by
    intro i j hij
    have hlt : Nat.nth P i < Nat.nth P j := Nat.nth_strictMono hPinf hij
    have hpos : 1 ≤ Nat.nth P i := hPpos _ (Nat.nth_mem_of_infinite hPinf i)
    show 3 * Nat.nth P i - 1 < 3 * Nat.nth P j - 1
    omega
  have hfg : ∀ i, ∃ j, g j = f i := by
    intro i
    have hQi : Q (Nat.nth Q i) := Nat.nth_mem_of_infinite hQinf i
    rcases (hQ (Nat.nth Q i)).mp hQi with ⟨m, hmP, hEq⟩
    refine ⟨Nat.count P m, ?_⟩
    show 3 * Nat.nth P (Nat.count P m) - 1 = Nat.nth Q i
    rw [Nat.nth_count hmP, ← hEq]
  have hgf : ∀ i, ∃ j, f j = g i := by
    intro i
    have hPi : P (Nat.nth P i) := Nat.nth_mem_of_infinite hPinf i
    have hQg : Q (g i) := (hQ (g i)).mpr ⟨Nat.nth P i, hPi, rfl⟩
    exact ⟨Nat.count Q (g i), Nat.nth_count hQg⟩
  exact strictMono_eq_of_same_range hf hg hfg hgf

/-- Direct formula relating `A026231(n)` to the `n`-th `1`-position of `A189640`:
`A026231(n) = 3 * a189640OnePos(n) - 1` for all `n ≥ 1`. -/
theorem a026231_eq_three_mul_onePos_sub_one (n : ℕ) (hn : 1 ≤ n) :
    a026231 n = 3 * a189640OnePos n - 1 := by
  have hne : n ≠ 0 := by omega
  simp only [a026231, a189640OnePos, hne, ↓reduceIte]
  exact nth_three_mul_sub_one a189640_one_infinite (fun _ hm => hm.1) a026231_pred_iff (n - 1)

private theorem a189640OnePos_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ a189640OnePos n := by
  have hne : n ≠ 0 := by omega
  simp only [a189640OnePos, hne, ↓reduceIte]
  exact (Nat.nth_mem_of_infinite a189640_one_infinite (n - 1)).1

/-! ### 6. Pinned Theorems (`PIN-C018.md` v1) -/

/-- Integrality theorem: for all `n ≥ 1`, `A026231(n) % 3 = 2`, ensuring exact
division by `3` in `A026232(n) = (A026231(n) + 1) / 3`. -/
theorem a026231_mod_three (n : ℕ) (hn : 1 ≤ n) :
    a026231 n % 3 = 2 := by
  rw [a026231_eq_three_mul_onePos_sub_one n hn]
  have hpos := a189640OnePos_pos n hn
  omega

/-- Primary C018 positional identity: for all `n ≥ 1`, the `n`-th 1-based
`1`-position of `A189640` equals `A026232(n)`. -/
theorem a189640_onePos_eq_a026232 (n : ℕ) (hn : 1 ≤ n) :
    a189640OnePos n = a026232 n := by
  have hne : n ≠ 0 := by omega
  simp only [a026232, hne, ↓reduceIte]
  rw [a026231_eq_three_mul_onePos_sub_one n hn]
  have hpos := a189640OnePos_pos n hn
  omega

/-! ### 7. Non-Vacuity & Offset-1 Calibration (`PIN-C018.md` Fidelity Note 3) -/

theorem a026166_eight : a026166 8 = 6 :=
  lrFill_eq_of_lrState goodLR_h66 (m := 6) rfl

theorem a026142_eight : a026142 8 = 5 :=
  lrFill_eq_of_lrState goodLR_h42 (m := 5) rfl

theorem a189640OnePos_one : a189640OnePos 1 = 3 := by
  classical
  let P : ℕ → Prop := fun k => 1 ≤ k ∧ a189640 k = 1
  have hP3 : P 3 := ⟨by omega, a189640_three_mul_add_three 0⟩
  have hle : Nat.nth P 0 ≤ 3 := by
    calc Nat.nth P 0
        ≤ Nat.nth P (Nat.count P 3) :=
          (Nat.nth_strictMono a189640_one_infinite).monotone (Nat.zero_le _)
      _ = 3 := Nat.nth_count hP3
  have hge : 3 ≤ Nat.nth P 0 := by
    have hP0 : P (Nat.nth P 0) := Nat.nth_mem_of_infinite a189640_one_infinite 0
    by_contra hlt
    have hk_cases : Nat.nth P 0 = 0 ∨ Nat.nth P 0 = 1 ∨ Nat.nth P 0 = 2 := by omega
    rcases hk_cases with h | h | h
    · exact (by omega : ¬(1 ≤ 0)) (h ▸ hP0.1)
    · have h1 : a189640 1 = 1 := h ▸ hP0.2
      rw [a189640_one] at h1
      omega
    · have h2 : a189640 2 = 1 := h ▸ hP0.2
      rw [show (2 : ℕ) = 3 * 0 + 2 by rfl, a189640_three_mul_add_two 0] at h2
      omega
  have hnth : Nat.nth P 0 = 3 := le_antisymm hle hge
  simpa [a189640OnePos, P] using hnth

theorem c018_offset_one_calibration :
    a189640OnePos 1 = 3 ∧ a026231 1 = 8 ∧ a026232 1 = 3 ∧
      a026166 8 = 6 ∧ a026142 8 = 5 := by
  refine ⟨a189640OnePos_one, ?_, ?_, a026166_eight, a026142_eight⟩
  · rw [a026231_eq_three_mul_onePos_sub_one 1 le_rfl, a189640OnePos_one]
  · rw [← a189640_onePos_eq_a026232 1 le_rfl, a189640OnePos_one]

end MathProofs.SeamB.C018
