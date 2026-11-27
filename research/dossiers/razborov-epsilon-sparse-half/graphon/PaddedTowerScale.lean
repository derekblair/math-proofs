import PaddedRegularityTower
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory Filter Topology

namespace SparseHalfGraphon

def canonicalFuel (n : ℕ) := (n+1)^2
noncomputable def canonicalScale (n : ℕ) : ℝ := ((n : ℝ)+1)⁻¹

theorem canonicalScale_pos (n : ℕ) : 0 < canonicalScale n := by
  unfold canonicalScale
  positivity

theorem canonicalFuel_valid (n : ℕ) :
    1 < ((canonicalFuel n : ℝ)+1)*(canonicalScale n)^2 := by
  unfold canonicalFuel canonicalScale
  push_cast
  have h : 0 < ((n:ℝ)+1)^2 := by positivity
  rw [inv_pow, ← div_eq_mul_inv, lt_div_iff₀ h]
  linarith

theorem canonicalScale_tendsto : Tendsto canonicalScale atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp h |>.congr (fun n => by
    simp [canonicalScale])

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

theorem shrinking_marked_tower {k : ℕ} (hk : 0 < k)
    (m : X → Fin k) (hm : Measurable m)
    (K : Kernel X) (hμ : mass μ = 1) :
    ∃ A : PaddedTower (X := X) (towerCapacity k canonicalFuel),
      A.label 0 = m ∧
      ∀ n, CutBound μ K (blockKernel μ K (A.label (n+1)) (A.measurable_label (n+1)))
        (canonicalScale n) :=
  uniformly_padded_marked_tower μ hk m hm K hμ canonicalScale canonicalFuel
    canonicalScale_pos canonicalFuel_valid

#print axioms canonicalScale_tendsto
#print axioms shrinking_marked_tower
end SparseHalfGraphon
