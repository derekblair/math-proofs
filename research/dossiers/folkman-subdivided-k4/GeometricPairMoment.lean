import GeometricRootedShellLoss
import GeometricMarginals
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset
open scoped ENNReal
variable {J S : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace S]

def offDiagonal : Finset (J×J) := Finset.univ.filter (fun p => p.1≠p.2)

noncomputable def samplePairCount (P : Set (S×S)) (x : J→S) : ℝ≥0∞ := by
  classical
  exact ∑ p∈(offDiagonal : Finset (J×J)), (P.indicator (fun _ => (1:ℝ≥0∞))) (x p.1,x p.2)

theorem samplePairCount_measurable (P : Set (S×S)) (pm : MeasurableSet P) :
    Measurable (samplePairCount (J:=J) P) := by
  exact Finset.measurable_fun_sum _ (fun p _ => (measurable_const.indicator pm).comp
    ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)))

theorem distinct_pair_marginal (σ : Measure S) [IsProbabilityMeasure σ] (i j : J) (ij : i≠j) :
    MeasurePreserving (fun x : J→S => (x i,x j))
      (Measure.pi fun _ : J => σ) (σ.prod σ) := by
  let e : Fin 2 ↪ J := ⟨![i,j],by
    intro u v eq
    fin_cases u <;> fin_cases v <;> first | rfl | exact (ij eq).elim | exact (ij eq.symm).elim⟩
  have h := (measurePreserving_piFinTwo (fun _ : Fin 2 => σ)).comp
    (pi_embedding_measurePreserving σ e)
  convert h using 1
  rfl

theorem samplePairCount_expectation (σ : Measure S) [IsProbabilityMeasure σ]
    (P : Set (S×S)) (pm : MeasurableSet P) :
    (∫⁻ x, samplePairCount (J:=J) P x ∂(Measure.pi fun _ : J => σ)) =
      ((offDiagonal : Finset (J×J)).card:ℝ≥0∞) * (σ.prod σ) P := by
  classical
  unfold samplePairCount
  have mm (p : J×J) : Measurable (fun x : J→S => P.indicator (fun _ => (1:ℝ≥0∞))
      (x p.1,x p.2)) := (measurable_const.indicator pm).comp
        ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2))
  rw [lintegral_finsetSum _ (fun p _ => mm p)]
  calc
    _ = ∑ _p ∈ (offDiagonal : Finset (J×J)), (σ.prod σ) P := by
      apply Finset.sum_congr rfl
      intro p hp
      have h := distinct_pair_marginal σ p.1 p.2 (Finset.mem_filter.mp hp).2
      have u := h.lintegral_comp ((measurable_const : Measurable (fun _ : S×S => (1:ℝ≥0∞))).indicator pm)
      simp only [lintegral_indicator_const pm,one_mul] at u
      exact u
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

theorem samplePairCount_markov (σ : Measure S) [IsProbabilityMeasure σ]
    (P : Set (S×S)) (pm : MeasurableSet P) (B : ℝ≥0∞) (B0 : B ≠ 0) (Bt : B≠∞) :
    (Measure.pi fun _ : J => σ) {x | B≤samplePairCount (J:=J) P x} ≤
      (((offDiagonal : Finset (J×J)).card:ℝ≥0∞)*(σ.prod σ) P)/B := by
  rw [←samplePairCount_expectation σ P pm]
  exact meas_ge_le_lintegral_div (samplePairCount_measurable P pm).aemeasurable B0 Bt

#print axioms samplePairCount_expectation
#print axioms samplePairCount_markov
end RobustFolkman.GeometricGap
