/-
  DipMarch.lean — R247 dip-march theorem: sliding-window recurrence, same-gap persistence, break/reset/perfect-translate classification, φ-duality.

  Paper: papers/translation-march-dip-October-11-2026/
  Status: [PROVED] — sliding_window_up/down, continuation_iff, break_case, reset_case, perfect_case, phi_duality
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R262: local + bakkie exit 0, zero sorrys, axioms standard-only.
-/

/-
R254 / R247 — the dip-march theorem (sliding-window mechanics + φ-duality).
[Status: formalization of R247's hand proof; hole interpretation (R247 Cor. 3)
is OUT OF SCOPE pending R240(i)/R227 formalization — see note at end.]
Definitions: for a finite integer set W (the "shadow") and t : ℤ,
  window t  = Finset.Icc (1 - t) (184 - t)
  gapSet W t = window t \ W   (the window gap set G_t)
All results are pure finite-set algebra; no hypotheses on W.
Lean 4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/
import Mathlib

namespace DipMarch

/-- The sliding window at step t: I_t = [1-t, 184-t]. -/
def window (t : ℤ) : Finset ℤ := Finset.Icc (1 - t) (184 - t)

/-- The window gap set: G_t = I_t ∩ (ℤ ∖ W), as a finset. -/
def gapSet (W : Finset ℤ) (t : ℤ) : Finset ℤ := window t \ W

/-- Helper: removing a distinct singleton from a singleton is a no-op. -/
private theorem singleton_sdiff_singleton {g e : ℤ} (h : g ≠ e) :
    ({g} : Finset ℤ) \ {e} = {g} := by
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl, -⟩; rfl
  · intro hy; exact ⟨hy, by omega⟩

/-- Interval shift, upward: I_{t+1} is I_t minus its top element 184-t,
    plus the entering integer -t. Pure integer arithmetic. -/
private theorem window_shift_up (t x : ℤ) :
    (1 - (t + 1) ≤ x ∧ x ≤ 184 - (t + 1)) ↔
    ((1 - t ≤ x ∧ x ≤ 184 - t) ∧ x ≠ 184 - t) ∨ x = -t := by
  constructor
  · intro h
    by_cases hxe : x = -t
    · exact Or.inr hxe
    · refine Or.inl ⟨⟨by omega, by omega⟩, by omega⟩
  · rintro (⟨⟨h1, h2⟩, hne⟩ | rfl) <;> refine ⟨by omega, by omega⟩

/-- Interval shift, downward: I_{t-1} is I_t minus its bottom element 1-t,
    plus the entering integer 185-t. Pure integer arithmetic. -/
private theorem window_shift_down (t x : ℤ) :
    (1 - (t - 1) ≤ x ∧ x ≤ 184 - (t - 1)) ↔
    ((1 - t ≤ x ∧ x ≤ 184 - t) ∧ x ≠ 1 - t) ∨ x = 185 - t := by
  constructor
  · intro h
    by_cases hxe : x = 185 - t
    · exact Or.inr hxe
    · refine Or.inl ⟨⟨by omega, by omega⟩, by omega⟩
  · rintro (⟨⟨h1, h2⟩, hne⟩ | rfl) <;> refine ⟨by omega, by omega⟩

/-- R247 Lemma (sliding window, upward): G_{t+1} = (G_t ∖ {184-t}) ∪ E_t,
    E_t = {-t} if -t ∉ W else ∅. Pure combinatorics, no hypotheses on W. -/
theorem sliding_window_up (W : Finset ℤ) (t : ℤ) :
    gapSet W (t + 1) = (gapSet W t \ {184 - t}) ∪ (if -t ∈ W then ∅ else {-t}) := by
  ext x
  unfold gapSet window
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
  rw [window_shift_up t x]
  by_cases hW : -t ∈ W
  · rw [ite_eq_left hW]; simp only [Finset.notMem_empty, or_false]
    by_cases hx : x = -t
    · subst hx
      simp only [hW, not_true_eq_false, and_false, false_and]
    · simp only [hx, or_false]
      tauto
  · rw [ite_eq_right hW, Finset.mem_singleton]
    by_cases hx : x = -t
    · subst hx
      simp only [hW, not_false_eq_true, eq_self_iff_true, or_true, and_true, true_and]
    · simp only [hx, or_false]
      tauto

/-- R247 Lemma (sliding window, downward): G_{t−1} = (G_t ∖ {1-t}) ∪ E'_t,
    E'_t = {185−t} if 185−t ∉ W else ∅. -/
theorem sliding_window_down (W : Finset ℤ) (t : ℤ) :
    gapSet W (t - 1) = (gapSet W t \ {1 - t}) ∪ (if 185 - t ∈ W then ∅ else {185 - t}) := by
  ext x
  unfold gapSet window
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
  rw [window_shift_down t x]
  by_cases hW : 185 - t ∈ W
  · rw [ite_eq_left hW]; simp only [Finset.notMem_empty, or_false]
    by_cases hx : x = 185 - t
    · subst hx
      simp only [hW, not_true_eq_false, and_false, false_and]
    · simp only [hx, or_false]
      tauto
  · rw [ite_eq_right hW, Finset.mem_singleton]
    by_cases hx : x = 185 - t
    · subst hx
      simp only [hW, not_false_eq_true, eq_self_iff_true, or_true, and_true, true_and]
    · simp only [hx, or_false]
      tauto

/-- R247 Corollary 1 (same-gap persistence): clean single-gap windows persist
    their gap unless the gap exits at the top edge. -/
theorem same_gap_persistence (W : Finset ℤ) (t g g' : ℤ)
    (h1 : gapSet W t = {g}) (h2 : gapSet W (t + 1) = {g'}) :
    g' = g ∨ g = 184 - t := by
  by_cases h : g = 184 - t
  · exact Or.inr h
  · left
    have hL := sliding_window_up W t
    rw [h1, singleton_sdiff_singleton h, h2] at hL
    -- hL : {g'} = {g} ∪ (if -t ∈ W then ∅ else {-t})
    have hmem : g ∈ ({g'} : Finset ℤ) := by
      rw [hL]; exact Finset.mem_union_left _ (Finset.mem_singleton_self g)
    rw [Finset.mem_singleton] at hmem
    exact hmem.symm

/-- R247 Corollary 2 (continuation/break criterion, upward):
    under G_t = {g}, G_{t+1} = {g} iff the gap stays in-window and the
    entering integer is already in W. -/
theorem continuation_iff (W : Finset ℤ) (t g : ℤ) (h1 : gapSet W t = {g}) :
    gapSet W (t + 1) = {g} ↔ g ≤ 183 - t ∧ -t ∈ W := by
  have hL := sliding_window_up W t
  rw [h1] at hL
  have hgI : g ∈ Finset.Icc (1 - t) (184 - t) := by
    have hmem : g ∈ gapSet W t := by rw [h1]; exact Finset.mem_singleton_self g
    unfold gapSet window at hmem
    exact (Finset.mem_sdiff.mp hmem).1
  rw [Finset.mem_Icc] at hgI
  constructor
  · intro hcon
    by_cases hW : -t ∈ W
    · rw [if_pos hW, Finset.union_empty] at hL
      rw [hcon] at hL
      -- hL : {g} = {g} \ {184 - t}; hence g ≠ 184 - t
      have hne : g ≠ 184 - t := by
        intro heq
        have hmem : g ∈ ({g} : Finset ℤ) \ {184 - t} := by
          rw [← hL]; exact Finset.mem_singleton_self g
        rw [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_singleton] at hmem
        exact hmem.2 heq
      refine ⟨by omega, hW⟩
    · rw [if_neg hW, hcon] at hL
      -- -t ∈ G_{t+1} = {g}, so -t = g ∈ I_t — but -t < 1 - t. Contradiction.
      have hmem : -t ∈ ({g} : Finset ℤ) := by
        rw [hL]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      rw [Finset.mem_singleton] at hmem
      exfalso
      omega
  · rintro ⟨hle, hW⟩
    rw [if_pos hW, Finset.union_empty] at hL
    rw [hL]
    exact singleton_sdiff_singleton (by omega)

/-- R247 Corollary 2, case (a) — BREAK: gap stays in-window but the entering
    integer is new, so the window gains a second gap. -/
theorem break_case (W : Finset ℤ) (t g : ℤ) (h1 : gapSet W t = {g})
    (hle : g ≤ 183 - t) (hW : -t ∉ W) :
    gapSet W (t + 1) = {g, -t} := by
  have hL := sliding_window_up W t
  rw [h1, if_neg hW, singleton_sdiff_singleton (by omega),
    Finset.singleton_union] at hL
  exact hL

/-- R247 Corollary 2, case (b) — RESET: gap exits at the top edge and the
    entering integer is new; a fresh single gap appears. -/
theorem reset_case (W : Finset ℤ) (t g : ℤ) (h1 : gapSet W t = {g})
    (hedge : g = 184 - t) (hW : -t ∉ W) :
    gapSet W (t + 1) = {-t} := by
  have hL := sliding_window_up W t
  rw [h1, hedge, if_neg hW, Finset.sdiff_self, Finset.empty_union] at hL
  exact hL

/-- R247 Corollary 2, case (c) — PERFECT translate: gap exits at the top edge
    and the entering integer is already in W; the window is gap-free. -/
theorem perfect_case (W : Finset ℤ) (t g : ℤ) (h1 : gapSet W t = {g})
    (hedge : g = 184 - t) (hW : -t ∈ W) :
    gapSet W (t + 1) = ∅ := by
  have hL := sliding_window_up W t
  rw [h1, hedge, if_pos hW, Finset.sdiff_self, Finset.union_empty] at hL
  exact hL

/-- R247 Corollary 2 (continuation/break criterion, downward):
    under G_t = {g}, G_{t−1} = {g} iff the gap stays in-window and the
    entering integer 185−t is already in W. -/
theorem continuation_iff_down (W : Finset ℤ) (t g : ℤ) (h1 : gapSet W t = {g}) :
    gapSet W (t - 1) = {g} ↔ g ≥ 2 - t ∧ 185 - t ∈ W := by
  have hL := sliding_window_down W t
  rw [h1] at hL
  have hgI : g ∈ Finset.Icc (1 - t) (184 - t) := by
    have hmem : g ∈ gapSet W t := by rw [h1]; exact Finset.mem_singleton_self g
    unfold gapSet window at hmem
    exact (Finset.mem_sdiff.mp hmem).1
  rw [Finset.mem_Icc] at hgI
  constructor
  · intro hcon
    by_cases hW : 185 - t ∈ W
    · rw [if_pos hW, Finset.union_empty] at hL
      rw [hcon] at hL
      have hne : g ≠ 1 - t := by
        intro heq
        have hmem : g ∈ ({g} : Finset ℤ) \ {1 - t} := by
          rw [← hL]; exact Finset.mem_singleton_self g
        rw [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_singleton] at hmem
        exact hmem.2 heq
      refine ⟨by omega, hW⟩
    · rw [if_neg hW, hcon] at hL
      -- 185 - t ∈ G_{t−1} = {g}, so 185 - t = g ∈ I_t — but 185 - t > 184 - t.
      have hmem : 185 - t ∈ ({g} : Finset ℤ) := by
        rw [hL]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      rw [Finset.mem_singleton] at hmem
      exfalso
      omega
  · rintro ⟨hge, hW⟩
    rw [if_pos hW, Finset.union_empty] at hL
    rw [hL]
    exact singleton_sdiff_singleton (by omega)

/-- R247 Theorem (φ-duality): reflecting the shadow through φ(w) = 185 − w
    reflects gap windows: G_t(185 − W) = 185 − G_{−t}(W). Stated with the
    reflected shadow as hypothesis (the shadow transform W(φ(A)) = 185 − W(A)
    is R227/R240 territory, not formalized here). -/
theorem phi_duality (W : Finset ℤ) (t : ℤ) :
    gapSet (Finset.image (fun w => 185 - w) W) t =
    Finset.image (fun g => 185 - g) (gapSet W (-t)) := by
  ext x
  unfold gapSet window
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hnim⟩
    refine ⟨185 - x, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · omega
    · omega
    · intro hyW
      apply hnim
      exact ⟨185 - x, hyW, by ring⟩
    · show 185 - (185 - x) = x
      ring
  · rintro ⟨y, ⟨⟨hlo, hhi⟩, hyW⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · rintro ⟨w, hwW, hweq⟩
      apply hyW
      have hwy : w = y := by omega
      rw [← hwy]; exact hwW

/-
NOTE (scope): R247 Corollary 3 ("the march": constant-gap runs ⟹ holes march
1/step) interprets gaps as translate holes via R240(i) and R227's hole
definition, neither of which is formalized. It is NOT claimed here. The
gap-level content — sliding-window mechanics, same-gap persistence, the exact
continuation/break/reset criterion in both directions, and φ-duality — is
fully proved above with zero sorrys and only standard axioms.
-/

end DipMarch
