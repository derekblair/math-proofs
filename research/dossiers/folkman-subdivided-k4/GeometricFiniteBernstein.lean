import GeometricOperatorOrder
import SLT.RMT.MatBern

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Finset RMT
open scoped ENNReal Matrix.Norms.L2Operator

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

def finiteMatrixMean (μ : Measure Ω) {n : ℕ} (A : Ω → Matrix (Fin n) (Fin n) ℝ) :=
  weightedMatrix (fun ω => (μ {ω}).toReal) A

theorem finiteMatrixMean_integral {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin n) (Fin n) ℝ) :
    (∫ ω, A ω ∂μ)=finiteMatrixMean μ A := by
  rw [integral_fintype Integrable.of_finite]
  rfl

theorem finiteSingleton_total (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (∑ ω : Ω, (μ {ω}).toReal)=1 := by
  rw [←ENNReal.toReal_sum (fun ω _ => measure_ne_top μ {ω}),
    sum_measure_singleton,Finset.coe_univ,measure_univ,ENNReal.toReal_one]

noncomputable def centeredRankOne (μ : Measure Ω) {n : ℕ} (v : Ω→Fin n→ℝ) (ω : Ω) :=
  rankOneMat (v ω) - finiteMatrixMean μ (fun a => rankOneMat (v a))

theorem finite_rank_one_bernstein {n N : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (v : Fin N→Ω→Fin n→ℝ) (K T s : ℝ) (Kp : 0<K) (T0 : 0≤T) (sp : 0<s)
    (hn : 0<n)
    (bounded : ∀ i ω, ∑ j, (v i ω j)^2≤K)
    (meanBound : ∀ i, ‖finiteMatrixMean μ (fun ω => rankOneMat (v i ω))‖≤T)
    (ind : MatrixBernsteinIndependent (fun i => centeredRankOne μ (v i)) μ) :
    (μ {ω | ‖∑ i,centeredRankOne μ (v i) ω‖≥s}).toReal ≤
      matrixBernsteinTailBound n ((N:ℝ)*K*T) (K+T) s := by
  let C := fun i ω => rankOneMat (v i ω)
  let M := fun i => finiteMatrixMean μ (C i)
  let X := fun i => centeredRankOne μ (v i)
  have IX (i : Fin N) : Integrable (X i) μ := Integrable.of_finite
  have IX2 (i : Fin N) : Integrable (fun ω => (X i ω)^2) μ := Integrable.of_finite
  have zero (i : Fin N) : (∫ ω, X i ω ∂μ)=0 := by
    change (∫ ω, C i ω - M i ∂μ)=0
    rw [integral_sub Integrable.of_finite (integrable_const _),integral_const,
      show μ.real Set.univ=1 from by simp [Measure.real],one_smul,finiteMatrixMean_integral]
    exact sub_self _
  have sym (i : Fin N) : ∀ᵐ ω ∂μ, (X i ω).IsHermitian := by
    apply ae_of_all
    intro ω
    have pc : ∀ a, (C i a).PosSemidef := fun a => rankOneMat_psd _
    have pm : (M i).PosSemidef := weightedMatrix_psd _ _ (fun _ => ENNReal.toReal_nonneg) pc
    exact (pc ω).isHermitian.sub pm.isHermitian
  have bd (i : Fin N) : ∀ᵐ ω ∂μ, ‖X i ω‖≤K+T := by
    apply ae_of_all
    intro ω
    change ‖C i ω - M i‖≤K+T
    exact (norm_sub_le _ _).trans (add_le_add
      ((rankOneMat_operator_bound (v i ω)).trans (bounded i ω)) (meanBound i))
  have vb (i : Fin N) : ‖∫ ω, (X i ω)^2 ∂μ‖≤K*T := by
    rw [finiteMatrixMean_integral]
    have v := weighted_rank_one_variance_norm (fun ω => (μ {ω}).toReal) (v i) K Kp.le
      (fun _ => ENNReal.toReal_nonneg) (finiteSingleton_total μ) (bounded i)
    exact v.trans (mul_le_mul_of_nonneg_left (meanBound i) Kp.le)
  have var : matrixBernsteinVarianceProxy μ X≤(N:ℝ)*K*T := by
    unfold matrixBernsteinVarianceProxy matrixBernsteinVarianceMatrix
    calc
      _ ≤ ∑ i, ‖∫ ω, (X i ω)^2 ∂μ‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin N, K*T := Finset.sum_le_sum (fun i _ => vb i)
      _ = _ := by simp [mul_assoc]
  have b := matrix_bernstein_inequality_hdp_all X μ (K+T) hn ind IX IX2 zero sym bd s sp.le
  refine b.trans ?_
  unfold matrixBernsteinTailBound
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have v0 := matrixBernsteinVarianceProxy_nonneg μ X
  have den : 0<matrixBernsteinVarianceProxy μ X+(K+T)*s/3 := by positivity
  have dv : matrixBernsteinVarianceProxy μ X+(K+T)*s/3≤(N:ℝ)*K*T+(K+T)*s/3 :=
    add_le_add_left var _
  rw [neg_div,neg_div]
  exact neg_le_neg (div_le_div_of_nonneg_left (by positivity) den dv)

#print axioms finite_rank_one_bernstein
end RobustFolkman.GeometricGap
