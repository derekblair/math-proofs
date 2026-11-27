import GraphonMantel
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set
open scoped ENNReal

namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]

/-- A uniform bound on the signed integral over each measurable set
controls the full L¹ norm with factor two. -/
theorem L1_from_set_integrals (μ : Measure X) {f : X → ℝ}
    (hf : Measurable f) (hfi : Integrable f μ) (ε : ℝ)
    (h : ∀ S : Set X, MeasurableSet S → |∫ x in S, f x ∂μ|≤ε) :
    (∫ x, |f x| ∂μ)≤2*ε := by
  have hp := h {x | 0≤f x} (measurableSet_le measurable_const hf)
  have hn := h {x | f x≤0} (measurableSet_le hf measurable_const)
  have h₁ := (abs_le.mp hp).2
  have h₂ := (abs_le.mp hn).1
  have he := integral_norm_eq_pos_sub_neg hfi
  simp only [Real.norm_eq_abs] at he
  rw [he]
  linarith

/-- Our cut distance arguments use the unnormalized rectangle bound. -/
def CutBound (μ : Measure X) (K J : Kernel X) (ε : ℝ) : Prop :=
  ∀ S T : Set X, MeasurableSet S → MeasurableSet T →
    |∫ x in S, ∫ y in T, K.W (x,y)-J.W (x,y) ∂μ ∂μ| ≤ ε

/-- Convergence in cut norm gives L¹ convergence of degrees into any one
fixed measurable part, uniformly over the choice of that part. -/
theorem cut_degree_L1 (μ : Measure X) [IsFiniteMeasure μ]
    (K J : Kernel X) (ε : ℝ) (hcut : CutBound μ K J ε)
    (T : Set X) (hT : MeasurableSet T) :
    (∫ x, |deg (μ.restrict T) K x-deg (μ.restrict T) J x| ∂μ)≤2*ε := by
  let ν := μ.restrict T
  have iK : Integrable (deg ν K) μ :=
    integrable_bounded μ (deg_measurable ν K) (deg_nonneg ν K) (deg_le_mass ν K)
  have iJ : Integrable (deg ν J) μ :=
    integrable_bounded μ (deg_measurable ν J) (deg_nonneg ν J) (deg_le_mass ν J)
  let f : X→ℝ := fun x => deg ν K x-deg ν J x
  change (∫ x, |f x| ∂μ) ≤ 2*ε
  apply L1_from_set_integrals μ ((deg_measurable ν K).sub (deg_measurable ν J))
    (iK.sub iJ) ε
  intro S hS
  have he (x : X) : f x=(∫ y in T, K.W (x,y)-J.W (x,y) ∂μ) := by
    rw [integral_sub (row_integrable ν K x) (row_integrable ν J x)]
    rfl
  change |∫ x in S, f x ∂μ|≤ε
  simpa only [he] using hcut S T hS hT

#print axioms cut_degree_L1
end SparseHalfGraphon
