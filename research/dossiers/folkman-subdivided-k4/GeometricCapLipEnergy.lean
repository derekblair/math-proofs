import GeometricCapAveraging
import GeometricPopulationPower

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace NNReal ENNReal
variable {S : Type*} [MeasurableSpace S]

noncomputable def energyNorm (μ : Measure S) (f : S→ℝ) : ℝ :=
  Real.sqrt (∫ x, (f x)^2 ∂μ)

theorem energyNorm_sq (μ : Measure S) (f : S→ℝ) :
    (energyNorm μ f)^2=∫ x,(f x)^2 ∂μ := by
  unfold energyNorm
  exact Real.sq_sqrt (integral_nonneg fun z => sq_nonneg _)

theorem energy_cauchy (μ : Measure S) (f g : S→ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)≤energyNorm μ f*energyNorm μ g := by
  have lip : (2:ℝ).HolderConjugate 2 := Real.holderConjugate_iff.2 ⟨by norm_num,by norm_num⟩
  have h := integral_mul_norm_le_Lp_mul_Lq (μ:=μ) lip
    (by simpa using hf : MemLp f (ENNReal.ofReal (2:ℝ)) μ)
    (by simpa using hg : MemLp g (ENNReal.ofReal (2:ℝ)) μ)
  have n := norm_integral_le_integral_norm (μ:=μ) (fun x => f x*g x)
  simp only [norm_mul] at n
  refine ((le_abs_self _).trans n).trans ?_
  unfold energyNorm
  simp only [Real.sqrt_eq_rpow,Real.rpow_two,Real.norm_eq_abs,sq_abs] at h ⊢
  exact h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem lipschitz_sphere_bound (f : UnitSphere E→ℝ) (L : ℝ≥0)
    (h : LipschitzWith L f) (a x : UnitSphere E) :
    ‖f x‖≤ 2*(L:ℝ)+‖f a‖ := by
  have g := h.dist_le_mul x a
  rw [dist_eq_norm] at g
  have e := mul_le_mul_of_nonneg_left (unit_sphere_dist_le_two x a) L.coe_nonneg
  calc
    _ = ‖(f x-f a)+f a‖ := by ring_nf
    _ ≤ ‖f x-f a‖+‖f a‖ := norm_add_le _ _
    _ ≤ _ := by linarith only [g,e]

theorem centered_lipschitz_bound (f : UnitSphere E→ℝ) (L : ℝ≥0)
    (h : LipschitzWith L f) (x : UnitSphere E)
    (zero : ∫ y,f y ∂uniformSphere (volume : Measure E)=0) :
    ‖f x‖≤2*(L:ℝ) := by
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  have eq : (∫ y, f x - f y ∂σ)=f x := by
    rw [integral_sub (integrable_const _) (integrable_lipschitz_sphere σ f L h x),
      integral_const,show σ.real univ=1 by simp [Measure.real],one_smul,zero,sub_zero]
  have bb (y : UnitSphere E) : ‖f x-f y‖≤2*(L:ℝ) := by
    have z := h.dist_le_mul x y
    rw [dist_eq_norm] at z
    nlinarith only [z,mul_le_mul_of_nonneg_left (unit_sphere_dist_le_two x y) L.coe_nonneg]
  have b := norm_integral_le_of_norm_le_const (ae_of_all σ bb)
  rw [eq,show σ.real univ=1 by simp [Measure.real],mul_one] at b
  exact b

noncomputable def capOrbit (t : ℝ) (f : UnitSphere E→ℝ) : ℕ→UnitSphere E→ℝ
  | 0 => f
  | k+1 => capAverage t (capOrbit t f k)

/-- Actual spherical cap averaging contracts L² on centered Lipschitz
tests by the checked dimension-dependent Lipschitz factor. -/
theorem cap_l2_contraction_lipschitz (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (large : 3≤(n:ℝ)/2)
    (dense : 1≤4*((n:ℝ)/2)*t^2) (a : UnitSphere E)
    (f : UnitSphere E→ℝ) (L : ℝ≥0) (lip : LipschitzWith L f)
    (center : ∫ x,f x ∂uniformSphere (volume : Measure E)=0) :
    let σ := uniformSphere (volume : Measure E)
    energyNorm σ (capAverage t f)≤Real.sqrt (squaredCapContraction n t)*energyNorm σ f := by
  intro σ
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let ρ : ℝ≥0 := ⟨Real.sqrt (squaredCapContraction n t),Real.sqrt_nonneg _⟩
  let F := capOrbit t f
  have t0 : -1<t := by linarith only [tp]
  have t1 : t<1 := by linarith only [ts]
  have Fl (k : ℕ) : LipschitzWith (L*ρ^k) (F k) := by
    induction k with
    | zero => simpa [F,capOrbit] using lip
    | succ k ih =>
      apply LipschitzWith.of_dist_le_mul
      intro x y
      have h := cap_average_pointwise_lipschitz n dim t tp ts large dense (F k) (L*ρ^k) ih x y
      change dist (capAverage t (F k) x) (capAverage t (F k) y)≤_
      have e : ((L*ρ^(k+1):ℝ≥0):ℝ)*dist x y =
          ((L*ρ^k:ℝ≥0):ℝ)*Real.sqrt (squaredCapContraction n t)*dist x y := by
        simp only [NNReal.coe_mul, NNReal.coe_pow, pow_succ]
        change _ = (L:ℝ)*(ρ:ℝ)^k*(ρ:ℝ)*dist x y
        ring
      rw [e]
      exact h
  let B := 2*(L:ℝ)+‖f a‖
  have B0 : 0≤B := by dsimp [B]; positivity
  have Fb (k : ℕ) : ∀ x : UnitSphere E, ‖F k x‖≤B := by
    induction k with
    | zero => exact lipschitz_sphere_bound f L lip a
    | succ k ih => exact capAverage_bound t t0 t1 _ B ih
  have Fm (k : ℕ) : Measurable (F k) := (Fl k).continuous.measurable
  have Fc (k : ℕ) : (∫ x,F k x ∂σ)=0 := by
    induction k with
    | zero => exact center
    | succ k ih =>
      change (∫ x,capAverage t (F k) x ∂σ)=0
      rw [capAverage_stationary_bounded t t0 t1 a (F k) (Fm k) B B0 (Fb k),ih]
  let u := fun k => energyNorm σ (F k)
  have ub (k : ℕ) : u k≤(2*(L:ℝ))*(ρ:ℝ)^k := by
    have B1 : 0≤2*(L:ℝ)*(ρ:ℝ)^k := by positivity
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) B1).1
    change (energyNorm σ (F k))^2≤_
    rw [energyNorm_sq]
    have q (x : UnitSphere E) : ‖F k x‖≤2*(L:ℝ)*(ρ:ℝ)^k := by
      have h := centered_lipschitz_bound (F k) _ (Fl k) x (Fc k)
      push_cast at h
      simpa [mul_assoc] using h
    have z := integral_mono (bounded_square_integrable (F k) (Fm k) B B0 (Fb k) σ)
      (integrable_const ((2*(L:ℝ)*(ρ:ℝ)^k)^2))
      (fun x => by
        have b := pow_le_pow_left₀ (norm_nonneg _) (q x) 2
        simpa [Real.norm_eq_abs,sq_abs] using b)
    rw [integral_const,show σ.real univ=1 by simp [Measure.real],one_smul] at z
    exact z
  have cv (k : ℕ) : (u (k+1))^2≤u k*u (k+2) := by
    have h := capAverage_symmetry_bounded t a (F k) (F (k+1)) (Fm k) (Fm (k+1))
      B B B0 B0 (Fb k) (Fb (k+1))
    change (∫ x,F k x*F (k+2) x ∂σ)=∫ x,F (k+1) x*F (k+1) x ∂σ at h
    change (energyNorm σ (F (k+1)))^2≤_
    rw [energyNorm_sq]
    simp_rw [pow_two]
    rw [←h]
    exact energy_cauchy σ _ _
      (MemLp.of_bound (Fm k).aestronglyMeasurable B (ae_of_all _ (Fb k)))
      (MemLp.of_bound (Fm (k+2)).aestronglyMeasurable B (ae_of_all _ (Fb (k+2))))
  change u 1≤(ρ:ℝ)*u 0
  by_cases h : 0<u 0
  · exact first_step_of_log_convex u ρ (2*(L:ℝ)) ρ.coe_nonneg h cv ub
  · have q := capAverage_l2_bounded t t0 t1 a f lip.continuous.measurable B B0 (Fb 0)
    have u0 : u 0=0 := le_antisymm (le_of_not_gt h) (Real.sqrt_nonneg _)
    change u 1≤_
    have q' : u 1≤u 0 := Real.sqrt_le_sqrt q
    rw [u0,mul_zero] at *
    exact q'

#print axioms cap_l2_contraction_lipschitz
end RobustFolkman.GeometricGap
