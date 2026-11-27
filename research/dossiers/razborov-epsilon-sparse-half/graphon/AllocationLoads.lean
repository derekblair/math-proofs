import SetAllocation

open Set MeasureTheory Function Filter
open scoped ENNReal
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma load_add (W : Kernel X) (d e : X→ℝ) (hd : BMeas d) (he : BMeas e) (v : X) :
    load μ W (d+e) v=load μ W d v+load μ W e v := by
  have bw : BMeas (fun x => W.W (v,x)) :=
    BMeas.of_unit (rowMeasurable W v) (fun _=>W.nonneg _) (fun _=>W.le_one _)
  have id : Integrable (fun x=>d x*W.W (v,x)) μ := bMeas_integrable μ (hd.mul bw)
  have ie : Integrable (fun x=>e x*W.W (v,x)) μ := bMeas_integrable μ (he.mul bw)
  unfold load
  simp only [Pi.add_apply,add_mul,integral_add id ie]

lemma load_le_mass_of_support (W : Kernel X) (v : X) (S : Set X) (hS : MeasurableSet S)
    (D : X→ℝ) (hD : BMeas D) (h₀ : ∀ x, 0≤D x) (h₁ : ∀ x, D x≤1)
    (hz : ∀ x∉S, D x=0) :
    load μ W D v≤μ.real (rowSupport W v S) := by
  classical
  let R := rowSupport W v S
  have hR := rowSupport_meas W v hS
  have bw := BMeas.of_unit (rowMeasurable W v) (fun _=>W.nonneg _) (fun _=>W.le_one _)
  have hi := integral_mono (bMeas_integrable μ (hD.mul bw))
    ((integrable_const (1:ℝ)).indicator hR) (fun x => by
      change D x*W.W (v,x)≤R.indicator (fun _=>1) x
      by_cases h : x∈R
      · rw [indicator_of_mem h]
        calc
          D x*W.W (v,x) ≤ 1*W.W (v,x) := mul_le_mul_of_nonneg_right (h₁ x) (W.nonneg _)
          _ ≤ 1 := by simpa only [one_mul] using W.le_one (v,x)
      · rw [indicator_of_notMem h]
        by_cases hs : x∈S
        · have hw : ¬ 0<W.W (v,x) := fun hpos=>h ⟨hs,hpos⟩
          exact mul_nonpos_of_nonneg_of_nonpos (h₀ x) (le_of_not_gt hw)
        · simp [hz x hs])
  change load μ W D v≤∫ x,R.indicator (fun _=>(1:ℝ)) x ∂μ at hi
  rwa [integral_indicator hR,setIntegral_const,smul_eq_mul,mul_one] at hi

lemma load_le_allocSet (W : Kernel X) (v : X) (S : Set X) (hS : MeasurableSet S)
    (q : ℝ) (h₀ : 0≤q) (hq : q≤μ.real S) :
    load μ W (allocSet μ S q) v ≤ q := by
  have hI := allocSet_bmeas μ S hS q h₀ hq
  have bw := BMeas.of_unit (rowMeasurable W v) (fun _=>W.nonneg _) (fun _=>W.le_one _)
  have h := integral_mono (bMeas_integrable μ (hI.mul bw)) (bMeas_integrable μ hI)
    (fun x=>by
      change allocSet μ S q x * W.W (v,x) ≤ allocSet μ S q x
      exact (mul_le_mul_of_nonneg_left (W.le_one _) (allocSet_nn μ S q h₀ x)).trans_eq (mul_one _))
  change load μ W (allocSet μ S q) v≤_ at h
  rwa [allocSet_mass μ S hS q h₀ hq] at h

#print axioms load_le_mass_of_support
#print axioms load_le_allocSet
end SparseHalfGraphon
