import Mathlib.Tactic

open scoped BigOperators

namespace MonotonePowerProjection

/-- If all independent selections of route segments give the same total,
    each slot has a fixed contribution independent of its selector. -/
theorem slot_count_invariant {I C : Type*} [Fintype I] [DecidableEq I]
    (count : C → I → ℕ) (Q : ℕ)
    (h : ∀ f : I → C, ∑ i, count (f i) i = Q)
    (x y : C) (i : I) : count x i = count y i := by
  let f : I → C := Function.update (fun _ => x) i y
  have hf := h f
  have hx := h (fun _ => x)
  rw [← Finset.sum_erase_add Finset.univ (fun j => count (f j) j) (Finset.mem_univ i)] at hf
  rw [← Finset.sum_erase_add Finset.univ (fun j => count x j) (Finset.mem_univ i)] at hx
  have hrest :
      (∑ j ∈ Finset.univ.erase i, count (f j) j) =
        ∑ j ∈ Finset.univ.erase i, count x j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show f j = x by
      exact Function.update_of_ne ((Finset.mem_erase.mp hj).1) y (fun _ => x)]
  rw [hrest, show f i = y by exact Function.update_self i y (fun _ => x)] at hf
  omega

/-- If independent route choices may never combine different positive colors,
    the fixed positive contributions are concentrated in exactly one slot. -/
theorem color_concentrates {I C : Type*} [Fintype I] [DecidableEq I]
    (count : C → I → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (x y : C) (hxy : x ≠ y)
    (hs : ∀ f : I → C, ∑ i, count (f i) i = Q)
    (hm : ∀ (f : I → C) (i j : I), i ≠ j →
      0 < count (f i) i → 0 < count (f j) j → f i = f j) :
    ∃ i : I, (∀ c : C, count c i = Q) ∧
      ∀ c j, j ≠ i → count c j = 0 := by
  have hex : ∃ i : I, 0 < count x i := by
    by_contra h'
    push Not at h'
    have hz : ∀ i, count x i = 0 := by
      intro i
      specialize h' i
      omega
    have ht := hs (fun _ => x)
    simp [hz] at ht
    omega
  obtain ⟨i, hi⟩ := hex
  have rest : ∀ j : I, j ≠ i → count x j = 0 := by
    intro j hj
    by_contra h'
    let f : I → C := Function.update (fun _ => y) i x
    have fi : f i = x := Function.update_self i x (fun _ => y)
    have fj : f j = y := Function.update_of_ne hj x (fun _ => y)
    have hg : count x j = count y j := slot_count_invariant count Q hs x y j
    have hcol := hm f i j (Ne.symm hj) (by simpa [fi] using hi) (by
      rw [fj, ← hg]
      omega)
    exact hxy (fi.symm.trans (hcol.trans fj))
  have hiQ : count x i = Q := by
    have ht := hs (fun _ => x)
    rw [Finset.sum_eq_single i (fun j _ hj => rest j hj) (by simp)] at ht
    exact ht
  exact ⟨i, fun c => (slot_count_invariant count Q hs c x i).trans hiQ,
    fun c j hj => (slot_count_invariant count Q hs c x j).trans (rest j hj)⟩

#print axioms slot_count_invariant
#print axioms color_concentrates

/-- Mixed-color exclusion alone forces a common slot, even when positive
    totals vary with the color. -/
theorem unequal_degree_color_concentrates {I C : Type*} [DecidableEq I]
    (count : C → I → ℕ) (x y : C) (hxy : x ≠ y)
    (nonempty : ∀ c : C, ∃ i : I, 0 < count c i)
    (hm : ∀ (f : I → C) (i j : I), i ≠ j →
      0 < count (f i) i → 0 < count (f j) j → f i = f j) :
    ∃ i : I, ∀ c j, 0 < count c j → j = i := by
  classical
  have eq_slot (a b : C) (i j : I) (hab : a ≠ b)
      (ha : 0 < count a i) (hb : 0 < count b j) : i = j := by
    by_contra hij
    let f : I → C := Function.update (fun _ => b) i a
    have fi : f i = a := Function.update_self i a (fun _ => b)
    have fj : f j = b := Function.update_of_ne (Ne.symm hij) a (fun _ => b)
    exact hab (fi.symm.trans ((hm f i j hij (by simpa [fi] using ha)
      (by simpa [fj] using hb)).trans fj))
  obtain ⟨i, hi⟩ := nonempty x
  obtain ⟨k, hk⟩ := nonempty y
  have hik := eq_slot x y i k hxy hi hk
  refine ⟨i, ?_⟩
  intro c j hj
  by_cases hcx : c = x
  · subst c
    exact (eq_slot x y j k hxy hj hk).trans hik.symm
  · exact eq_slot c x j i hcx hj hi

#print axioms unequal_degree_color_concentrates

end MonotonePowerProjection
