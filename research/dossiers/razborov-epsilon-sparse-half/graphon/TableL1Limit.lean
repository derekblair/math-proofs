import BlockEnergyIncrement
import TableDiagonal
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Set Function Filter Topology
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma bmeas_abs {f : X→ℝ} (hf : BMeas f) : BMeas (fun x => |f x|) := by
  obtain ⟨hm,C,hC⟩ := hf
  exact ⟨continuous_abs.measurable.comp hm,C,fun x=>by simpa only [abs_abs] using hC x⟩

lemma dist_real_L1 (f g : X→ℝ) (iF : Integrable f μ) (iG : Integrable g μ) :
    dist (iF.toL1 f) (iG.toL1 g)=∫ x, |f x-g x| ∂μ := by
  rw [dist_eq_norm,← Integrable.toL1_sub f g iF iG,
    Integrable.norm_toL1_eq_lintegral_enorm]
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using
    (integral_norm_eq_lintegral_enorm (f:=f-g) (iF.aestronglyMeasurable.sub iG.aestronglyMeasurable)).symm

lemma L1_squared_le_second_moment (f : X→ℝ) (hf : BMeas f) (hμ : mass μ=1) :
    (∫ x, |f x| ∂μ)^2≤∫ x, (f x)^2 ∂μ := by
  have hV : (∫ _ : X, (1:ℝ)^2 ∂μ)≤1 := by
    rw [integral_const,smul_eq_mul]
    change mass μ*(1:ℝ)^2≤1
    simp [hμ]
  have h := test_second_moment μ (fun x=>|f x|) (fun _=>1)
    (bmeas_abs hf) (BMeas.const 1) hV
  simpa only [mul_one,sq_abs] using h

/-- Consistent nested cell masses turn energy differences into a
complete L¹ limit. The abstract identities may come from limit tables. -/
theorem coherent_table_L1_limit (hμ : mass μ=1)
    (f : ℕ→X→ℝ) (hf : ∀ n, BMeas (f n)) (E : ℕ→ℝ)
    (hmono : Monotone E) (hE : ∀ n, E n≤1)
    (hgap : ∀ i j, i≤j →
      (∫ x, (f j x-f i x)^2 ∂μ)=E j-E i) :
    ∃ F : X →₁[μ] ℝ,
      Tendsto (fun n => (bMeas_integrable μ (hf n)).toL1 (f n)) atTop (𝓝 F) := by
  let G := fun n => (bMeas_integrable μ (hf n)).toL1 (f n)
  have hB : BddAbove (range E) := by
    refine ⟨1,?_⟩
    rintro _ ⟨n,rfl⟩
    exact hE n
  have hEc : CauchySeq E := (tendsto_atTop_ciSup hmono hB).cauchySeq
  have hG : CauchySeq G := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hEc (ε^2) (by positivity)
    refine ⟨N,?_⟩
    have hab : ∀ i≥N, ∀ j≥N, i≤j → dist (G j) (G i)<ε := by
      intro i hi j hj hij
      have hd := hN j hj i hi
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hmono hij))] at hd
      have h := L1_squared_le_second_moment μ (f j-f i) ((hf j).sub (hf i)) hμ
      change (∫ x, |f j x-f i x| ∂μ)^2≤∫ x, (f j x-f i x)^2 ∂μ at h
      rw [hgap i j hij,← dist_real_L1 μ (f j) (f i)
        (bMeas_integrable μ (hf j)) (bMeas_integrable μ (hf i))] at h
      change (dist (G j) (G i))^2≤_ at h
      by_contra! hn
      have hp := pow_le_pow_left₀ hε.le hn 2
      linarith
    intro i hi j hj
    rcases le_total i j with hij | hji
    · rw [dist_comm]; exact hab i hi j hj hij
    · exact hab j hj i hi hji
  exact cauchySeq_tendsto_of_complete hG

#print axioms coherent_table_L1_limit
end SparseHalfGraphon
