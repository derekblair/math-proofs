import BoxCore
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace DirectedBoxDSP

/-- Finite double count behind the central-third cut. Each subinterval carries
exactly those clipped arcs that span it. A per-arc total length bound is
enough, regardless of the number of clipped projection endpoints. -/
theorem cut_of_roster_projection_budget {I E : Type*} [DecidableEq E]
    (cells : Finset I) (arcs : Finset E) (roster : I → Finset E)
    (len : I → ℝ) (projection : E → ℝ) (W : ℝ) (k : ℕ)
    (hW : 0 < W)
    (cells_nonneg : ∀ i ∈ cells, 0 ≤ len i)
    (central : ∑ i ∈ cells, len i = W/3)
    (subset : ∀ i ∈ cells, roster i ⊆ arcs)
    (paid : ∀ e ∈ arcs, (∑ i ∈ cells.filter (fun i => e ∈ roster i), len i) ≤ projection e)
    (budget : (∑ e ∈ arcs, projection e) ≤ 3 * (k : ℝ) * W) :
    ∃ i ∈ cells, (roster i).card ≤ 9*k := by
  classical
  have hrow (i : I) (hi : i ∈ cells) : (roster i).card • len i =
      ∑ e ∈ arcs, if e ∈ roster i then len i else 0 := by
    rw [← Finset.sum_filter]
    have heq : arcs.filter (fun e => e ∈ roster i) = roster i := by
      ext e
      exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h =>
        Finset.mem_filter.mpr ⟨subset i hi h, h⟩⟩
    rw [heq, Finset.sum_const]
  have integ : (∑ i ∈ cells, ((roster i).card : ℝ) * len i) ≤ 3 * (k : ℝ) * W := by
    have h (i : I) (hi : i ∈ cells) : ((roster i).card : ℝ) * len i =
        ∑ e ∈ arcs, if e ∈ roster i then len i else 0 := by
      simpa [nsmul_eq_mul] using hrow i hi
    rw [Finset.sum_congr rfl h, Finset.sum_comm]
    simp_rw [← Finset.sum_filter]
    exact (Finset.sum_le_sum paid).trans budget
  apply BoxCore.good_subinterval cells len (fun i => (roster i).card) (9*k)
    cells_nonneg (by rw [central]; linarith)
  convert integ using 1
  rw [central, Nat.cast_mul]
  norm_num <;> ring

#print axioms cut_of_roster_projection_budget
end DirectedBoxDSP
