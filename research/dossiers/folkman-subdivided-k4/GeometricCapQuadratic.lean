import GeometricCenteredKernelL2

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem centered_cap_quadratic (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (large : 3≤(n:ℝ)/2)
    (dense : 1≤4*((n:ℝ)/2)*t^2) (a : UnitSphere E)
    (f : UnitSphere E→ℝ) (fm : Measurable f) (B : ℝ) (B0 : 0≤B) (bd : ∀ x, ‖f x‖≤B) :
    let σ := uniformSphere (volume : Measure E)
    let q := σ.real (capPoints t a)
    ‖∫ p : UnitSphere E×UnitSphere E, (capKernel t p.1 p.2-q)*(f p.1*f p.2) ∂(σ.prod σ)‖ ≤
      q*Real.sqrt (squaredCapContraction n t)*(energyNorm σ f)^2 := by
  intro σ q
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let K := fun p : UnitSphere E×UnitSphere E => capKernel t p.1 p.2-q
  have Km : Measurable K := (capKernel_joint_measurable t).sub measurable_const
  have Kb (p : UnitSphere E×UnitSphere E) : ‖K p‖ ≤ 1+‖q‖ :=
    (norm_sub_le _ _).trans (add_le_add_left (norm_capKernel_le_one t p.1 p.2) _)
  let H := fun p : UnitSphere E×UnitSphere E => K p * (f p.1*f p.2)
  have Hm : Measurable H := Km.mul ((fm.comp measurable_fst).mul (fm.comp measurable_snd))
  have HI : Integrable H (σ.prod σ) := by
    apply Integrable.of_bound Hm.aestronglyMeasurable ((1+‖q‖)*(B*B))
    apply ae_of_all
    intro p
    change ‖K p * (f p.1*f p.2)‖ ≤ _
    rw [norm_mul,norm_mul]
    exact mul_le_mul (Kb p) (mul_le_mul (bd p.1) (bd p.2) (norm_nonneg _) B0)
      (by positivity) (by positivity)
  let g := fun x : UnitSphere E => ∫ y, K (x,y)*f y ∂σ
  have gm : Measurable g :=
    (Km.mul (fm.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have gb (x : UnitSphere E) : ‖g x‖ ≤ (1+‖q‖)*B := by
    have z := norm_integral_le_of_norm_le_const (μ:=σ) (C:=(1+‖q‖)*B)
      (f:=fun y => K (x,y)*f y) (ae_of_all σ (fun y => by
        rw [norm_mul]
        exact mul_le_mul (Kb (x,y)) (bd y) (norm_nonneg _) (by positivity)))
    simpa [g,Measure.real] using z
  have gp : MemLp g 2 σ := MemLp.of_bound gm.aestronglyMeasurable _ (ae_of_all _ gb)
  have fp : MemLp f 2 σ := MemLp.of_bound fm.aestronglyMeasurable B (ae_of_all _ bd)
  have absC : ‖∫ x, f x*g x ∂σ‖ ≤ energyNorm σ f*energyNorm σ g := by
    rw [Real.norm_eq_abs,abs_le]
    constructor
    · have hh := energy_cauchy σ f (-g) fp gp.neg
      have he : energyNorm σ (-g)=energyNorm σ g := by
        unfold energyNorm
        simp only [Pi.neg_apply,neg_sq]
      rw [he] at hh
      simp only [Pi.neg_apply,mul_neg,integral_neg] at hh
      linarith
    · exact energy_cauchy σ f g fp gp
  have hh (x : UnitSphere E) : (∫ y, H (x,y) ∂σ)=f x*g x := by
    simp_rw [H,g,show ∀ a b c : ℝ,a*(b*c)=b*(a*c) from fun a b c => by ring,integral_const_mul]
  change ‖∫ p, H p ∂(σ.prod σ)‖ ≤ _
  rw [integral_prod H HI]
  simp_rw [hh]
  have con : energyNorm σ g ≤ q*Real.sqrt (squaredCapContraction n t)*energyNorm σ f :=
    centered_cap_energy n dim t tp ts large dense a f fm B B0 bd
  calc
    _ ≤ energyNorm σ f*energyNorm σ g := absC
    _ ≤ energyNorm σ f*(q*Real.sqrt (squaredCapContraction n t)*energyNorm σ f) :=
      mul_le_mul_of_nonneg_left con (Real.sqrt_nonneg _)
    _ = _ := by ring

#print axioms centered_cap_quadratic
end RobustFolkman.GeometricGap
