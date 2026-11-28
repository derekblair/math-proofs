import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

namespace DirectedBoxDSP

variable {F K : Type*} [Fintype F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Longest-side splits contract all side lengths after one coordinate block.
An individual shrinking step need not change the longest side length. -/
theorem longest_side_block_shrink (w : ℕ → F → K) (s : ℕ → F) (W : K)
    (hW : ∀ f, w 0 f ≤ W)
    (mon : ∀ n f, w (n+1) f ≤ w n f)
    (largest : ∀ n f, w n f ≤ w n (s n))
    (cut : ∀ n, w (n+1) (s n) ≤ (2/3 : K) * w n (s n)) :
    ∀ f, w (Fintype.card F) f ≤ (2/3 : K) * W := by
  classical
  let hi : ℕ → Finset F := fun n =>
    Finset.univ.filter fun f => (2/3 : K) * W < w n f
  have hi_mem (n : ℕ) (f : F) : f ∈ hi n ↔ (2/3 : K) * W < w n f := by
    simp [hi]
  have hbounded (n : ℕ) : ∀ f, w n f ≤ W := by
    induction n with
    | zero => exact hW
    | succ n ih => exact fun f => (mon n f).trans (ih f)
  have nest (n : ℕ) : hi (n+1) ⊆ hi n := by
    intro f hf
    exact (hi_mem n f).mpr (((hi_mem (n+1) f).mp hf).trans_le (mon n f))
  have absent (n : ℕ) : s n ∉ hi (n+1) := by
    have hm := mul_le_mul_of_nonneg_left (hbounded n (s n)) (by norm_num : 0 ≤ (2/3 : K))
    exact fun hx => not_lt_of_ge ((cut n).trans hm) ((hi_mem (n+1) (s n)).mp hx)
  have hd (n : ℕ) (hn : (hi n).Nonempty) : (hi (n+1)).card < (hi n).card := by
    obtain ⟨f, hf⟩ := hn
    have hsn : s n ∈ hi n :=
      (hi_mem n (s n)).mpr (((hi_mem n f).mp hf).trans_le (largest n f))
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨nest n, by
      intro h
      exact absent n (h.symm ▸ hsn)⟩)
  have hc (n : ℕ) : (hi n).card ≤ Fintype.card F - n := by
    induction n with
    | zero =>
      simpa using (Finset.card_le_card (Finset.subset_univ (hi 0)))
    | succ n ih =>
      by_cases hn : (hi n).Nonempty
      · have h := hd n hn
        omega
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn
        have hh := Finset.card_le_card (nest n)
        rw [he] at hh
        simp at hh
        simp [hh]
  intro f
  have hzero : (hi (Fintype.card F)).card = 0 := by
    have h := hc (Fintype.card F)
    omega
  exact le_of_not_gt fun h => by
    have hf := (hi_mem _ f).mpr h
    simpa [Finset.card_eq_zero.mp hzero] using hf

#print axioms longest_side_block_shrink
end DirectedBoxDSP
