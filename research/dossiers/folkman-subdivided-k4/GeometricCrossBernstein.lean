import GeometricIIDBernstein

namespace RobustFolkman.GeometricGap
open MeasureTheory ProbabilityTheory Matrix Finset RMT
open scoped ENNReal Matrix.Norms.L2Operator
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

noncomputable def truncatedCross {n k : ℕ} (K : Ω→Ω→ℝ) (x : Fin n→Ω)
    (good : Ω→Bool) (y : Fin k→Ω) : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => if good (y j) then rightColumn K x (y j) i else 0

theorem iid_truncated_cross_tail {n k : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω→Ω→ℝ) (x : Fin n→Ω) (good : Ω→Bool)
    (B T s : ℝ) (Bp : 0<B) (T0 : 0≤T) (sp : 0<s) (hn : 0<n)
    (bound : ∀ y, good y=true → ∑ i,(rightColumn K x y i)^2≤B)
    (left : ‖∑ i, rankOneMat (kernelFeature K (fun z => (μ {z}).toReal) (x i))‖≤T) :
    ((Measure.pi (fun _ : Fin k => μ)) {y |
      Real.sqrt ((k:ℝ)*T+s)<‖truncatedCross K x good y‖}).toReal ≤
      matrixBernsteinTailBound n ((k:ℝ)*B*T) (B+T) s := by
  let ν := Measure.pi (fun _ : Fin k => μ)
  let v : Ω→Fin n→ℝ := fun z => if good z then rightColumn K x z else 0
  let M := finiteMatrixMean μ (fun z => rankOneMat (v z))
  have G : ∀ z, ∑ i,(v z i)^2≤B := by
    intro z
    cases h : good z
    · simp [v,h,Bp.le]
    · simpa [v,h] using bound z h
  have P : ‖M‖≤T := (truncate_right_covariance K (fun z => (μ {z}).toReal) x
    (fun _ => ENNReal.toReal_nonneg) good).trans left
  have law := iid_finite_rank_one_bernstein (N:=k) μ v B T s Bp T0 sp hn G P
  apply le_trans ?_ law
  apply ENNReal.toReal_mono (measure_ne_top ν _)
  apply measure_mono
  intro y bad
  change Real.sqrt ((k:ℝ)*T+s)<‖truncatedCross K x good y‖ at bad
  change s≤‖(∑ i,rankOneMat (v (y i))) - (k:ℝ) • M‖
  by_contra! small
  let F := truncatedCross K x good y
  let A := ∑ j,rankOneMat (v (y j))
  have c : ‖A‖≤(k:ℝ)*T+s := by
    have eq : A=(A-(k:ℝ) • M)+(k:ℝ) • M := by abel
    have h : ‖A‖≤‖A-(k:ℝ) • M‖+‖(k:ℝ) • M‖ := by
      nth_rw 1 [eq]
      exact norm_add_le _ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤k)] at h
    have mm := mul_le_mul_of_nonneg_left P (by positivity : (0:ℝ)≤k)
    nlinarith only [small,h,mm]
  have e (i j) : F i j = v (y j) i := by
    change (if good (y j) then rightColumn K x (y j) i else 0) = (if good (y j) then rightColumn K x (y j) else 0) i
    split <;> rfl
  have d : (∑ j,rankOneMat (fun i => F i j))=A :=
    Finset.sum_congr rfl fun j _ => congrArg rankOneMat (funext fun i => e i j)
  have z : ‖F‖≤Real.sqrt ((k:ℝ)*T+s) := by
    apply columns_norm_bound F _ (Real.sqrt_nonneg _)
    rw [d,Real.sq_sqrt (by positivity)]
    exact c
  exact not_lt_of_ge z bad

#print axioms iid_truncated_cross_tail
end RobustFolkman.GeometricGap
