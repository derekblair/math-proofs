import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

namespace DirectedBoxDSP

/-- A finite instance has a positive separation scale, but the algorithm's
rank-based enumeration does not need to find or represent this scale. -/
theorem finite_positive_gap {E : Type*} [Fintype E] (value : E → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ e, 0 < value e → ε ≤ value e := by
  classical
  let s : Finset E := Finset.univ.filter (fun e => 0 < value e)
  by_cases hs : s.Nonempty
  · obtain ⟨e,he,hm⟩ := s.exists_min_image value hs
    exact ⟨value e, (Finset.mem_filter.mp he).2, fun j hj =>
      hm j (by simp [s,hj])⟩
  · refine ⟨1,zero_lt_one,?_⟩
    intro e he
    exact (hs ⟨e,by simp [s,he]⟩).elim

/-- Uniform multiplicative contraction eventually beats any positive
separation scale, irrespective of coefficient bit sizes. -/
theorem contraction_below (W ε : ℝ) (hW : 0 < W) (he : 0 < ε) :
    ∃ n : ℕ, (2/3 : ℝ)^n * W < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos he hW)
    (by norm_num : (2/3 : ℝ) < 1)
  exact ⟨n, (lt_div_iff₀ hW).mp hn⟩

#print axioms finite_positive_gap
#print axioms contraction_below
end DirectedBoxDSP
