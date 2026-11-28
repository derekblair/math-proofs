import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

namespace DirectedBoxDSP

variable {F K : Type*} [Fintype F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A segment from a strict interior point towards an outside point exits
a finite intersection of affine halfspaces at an actual face. Each index
is one inequality; the two signed coordinate bounds are the box case. -/
theorem finite_halfspace_exit
    (a b cap : F → K)
    (ha : ∀ i, a i < cap i)
    (hb : ∃ i, cap i < b i) :
    ∃ t : K, 0 < t ∧ t < 1 ∧
      (∀ i, a i + t * (b i - a i) ≤ cap i) ∧
      ∃ i, cap i < b i ∧ a i + t * (b i - a i) = cap i := by
  classical
  let s : Finset F := Finset.univ.filter fun i => cap i < b i
  let r : F → K := fun i => (cap i - a i) / (b i - a i)
  have hs : s.Nonempty := by
    obtain ⟨j, hj⟩ := hb
    exact ⟨j, by simp [s, hj]⟩
  obtain ⟨i, hi, hm⟩ := s.exists_min_image r hs
  have hbi : cap i < b i := (Finset.mem_filter.mp hi).2
  have hden : 0 < b i - a i := sub_pos.mpr ((ha i).trans hbi)
  have hpos : 0 < r i := div_pos (sub_pos.mpr (ha i)) hden
  have hlt : r i < 1 := (div_lt_iff₀ hden).mpr (by linarith)
  refine ⟨r i, hpos, hlt, ?_, ⟨i, hbi, ?_⟩⟩
  · intro j
    by_cases hj : cap j < b j
    · have hdenj : 0 < b j - a j := sub_pos.mpr ((ha j).trans hj)
      have hmin : r i ≤ r j := hm j (by simp [s, hj])
      have hmul := (le_div_iff₀ hdenj).mp hmin
      linarith
    · have hj' : b j ≤ cap j := le_of_not_gt hj
      have h1 : 0 ≤ (1 - r i) * (cap j - a j) :=
        mul_nonneg (sub_nonneg.mpr hlt.le) (sub_nonneg.mpr (ha j).le)
      have h2 : 0 ≤ r i * (cap j - b j) :=
        mul_nonneg hpos.le (sub_nonneg.mpr hj')
      linarith
  · have hmul : r i * (b i - a i) = cap i - a i :=
      (div_mul_cancel₀ _ hden.ne')
    linarith

#print axioms finite_halfspace_exit
end DirectedBoxDSP
