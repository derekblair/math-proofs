import CutExceptional

open MeasureTheory Set Function
namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

theorem row_shift_point (K : Kernel X) (S T : Set X) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (v : X) :
    |deg (μ.restrict S) K v-deg (μ.restrict T) K v|
      ≤μ.real (S\T)+μ.real (T\S) := by
  let f : X→ℝ := fun x=>K.W (v,x)
  have hf := row_integrable μ K v
  have hs : (∫ x in S∩T,f x ∂μ)+(∫ x in S\T,f x ∂μ)=∫ x in S,f x ∂μ :=
    integral_inter_add_sdiff hT hf.integrableOn
  have ht : (∫ x in S∩T,f x ∂μ)+(∫ x in T\S,f x ∂μ)=∫ x in T,f x ∂μ := by
    rw [inter_comm]
    exact integral_inter_add_sdiff hS hf.integrableOn
  have h₁ := deg_nonneg (μ.restrict (S\T)) K v
  have h₂ := deg_nonneg (μ.restrict (T\S)) K v
  have h₃ := deg_le_mass (μ.restrict (S\T)) K v
  have h₄ := deg_le_mass (μ.restrict (T\S)) K v
  simp only [mass,measureReal_restrict_apply_univ] at h₃ h₄
  change |(∫ x in S,f x ∂μ)-(∫ x in T,f x ∂μ)| ≤_
  rw [← hs,← ht,abs_le]
  change 0≤(∫ x in S\T,f x ∂μ) at h₁
  change 0≤(∫ x in T\S,f x ∂μ) at h₂
  change (∫ x in S\T,f x ∂μ)≤_ at h₃
  change (∫ x in T\S,f x ∂μ)≤_ at h₄
  constructor <;> linarith [measureReal_nonneg (μ:=μ) (s:=S\T),
    measureReal_nonneg (μ:=μ) (s:=T\S)]

/-- Marked-degree comparison under jointly changing the kernel and marked
partition, as happens on a sequence of coupling spaces. -/
theorem shifted_cut_degree_L1 (K J : Kernel X) (S T : Set X)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (ε : ℝ) (hc : CutBound μ K J ε) :
    (∫ v, |deg (μ.restrict S) K v-deg (μ.restrict T) J v| ∂μ)
      ≤2*ε+mass μ*(μ.real (S\T)+μ.real (T\S)) := by
  let a := deg (μ.restrict S) K
  let b := deg (μ.restrict S) J
  let c := deg (μ.restrict T) J
  have hA := deg_bmeas (μ.restrict S) K
  have hB := deg_bmeas (μ.restrict S) J
  have hC := deg_bmeas (μ.restrict T) J
  have hab : Integrable (fun v=>|a v-b v|) μ :=
    (bMeas_integrable μ (hA.sub hB)).abs
  have hac : Integrable (fun v=>|a v-c v|) μ :=
    (bMeas_integrable μ (hA.sub hC)).abs
  have hcb : Integrable (fun v=>|b v-c v|) μ :=
    (bMeas_integrable μ (hB.sub hC)).abs
  have hi := integral_mono hac (hab.add hcb) (fun v => abs_sub_le (a v) (b v) (c v))
  have hj := integral_mono hcb (integrable_const (μ:=μ) _)
    (row_shift_point μ J S T hS hT)
  change (∫ v, |a v-c v| ∂μ)≤∫ v, |a v-b v|+|b v-c v| ∂μ at hi
  rw [integral_add hab hcb] at hi
  rw [integral_const,smul_eq_mul] at hj
  have h0 := cut_degree_L1 μ K J ε hc S hS
  change (∫ v, |a v-b v| ∂μ)≤_ at h0
  change (∫ v, |b v-c v| ∂μ)≤mass μ*(μ.real (S\T)+μ.real (T\S)) at hj
  change (∫ v, |a v-c v| ∂μ)≤_
  linarith

#print axioms shifted_cut_degree_L1
end SparseHalfGraphon
