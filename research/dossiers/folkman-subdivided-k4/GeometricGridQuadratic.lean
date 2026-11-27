import GeometricFiniteGridMeasurable
import GeometricKernelPerturbation
import GeometricCapQuadratic

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped BigOperators ENNReal
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype I]

/-- Compress the centered spherical kernel to any finite measurable partition.
A cellwise approximation can change a bounded kernel by at most one on a
measurable exceptional set; the compression pays the square root of its mass. -/
theorem grid_centered_cap_quadratic (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (large : 3≤(n:ℝ)/2)
    (dense : 1≤4*((n:ℝ)/2)*t^2) (a : UnitSphere E)
    (code : UnitSphere E→I) (mc : ∀ i, MeasurableSet (code ⁻¹' {i}))
    (K : I→I→ℝ) (e : Set (UnitSphere E×UnitSphere E)) (em : MeasurableSet e)
    (err : ∀ z : UnitSphere E×UnitSphere E,
      ‖K (code z.1) (code z.2)-capKernel t z.1 z.2‖ ≤ e.indicator (fun _ => 1) z)
    (v : I→ℝ) :
    let σ := uniformSphere (volume : Measure E)
    let q := σ.real (capPoints t a)
    let p := fun i => σ.real (code ⁻¹' {i})
    ‖∑ i, ∑ j, Real.sqrt (p i)*Real.sqrt (p j)*(K i j-q)*(v i*v j)‖ ≤
      (q*Real.sqrt (squaredCapContraction n t)+Real.sqrt ((σ.prod σ).real e)) *
        ∑ i, (v i)^2 := by
  classical
  intro σ q p
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let ν := σ.prod σ
  let w := fun i => v i/Real.sqrt (p i)
  let f := fun x => w (code x)
  let B := ∑ i, ‖w i‖
  have fm : Measurable f := measurable_finite_code code mc w
  have B0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have fb (x) : ‖f x‖≤B := finite_code_bound code w x
  have cp := centered_cap_quadratic n dim t tp ts large dense a f fm B B0 fb
  have el := grid_energy_lift σ code mc v
  change energyNorm σ f ≤ _ at el
  have el2 : (energyNorm σ f)^2≤∑ i, (v i)^2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) el 2
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
  let D := fun z : UnitSphere E×UnitSphere E => K (code z.1) (code z.2)-capKernel t z.1 z.2
  have Dm : Measurable D := (measurable_pair_code code mc K).sub (capKernel_joint_measurable t)
  have ep := kernel_quadratic_perturbation σ e em D Dm err f fm B fb
  let H := fun z : UnitSphere E×UnitSphere E => (K (code z.1) (code z.2)-q)*(f z.1*f z.2)
  let U := fun z : UnitSphere E×UnitSphere E => (capKernel t z.1 z.2-q)*(f z.1*f z.2)
  let V := fun z : UnitSphere E×UnitSphere E => D z*(f z.1*f z.2)
  have UV : H=fun z => U z+V z := by funext z; dsimp [H,U,V,D]; ring
  have mm : Measurable (fun z : UnitSphere E×UnitSphere E => f z.1*f z.2) :=
    (fm.comp measurable_fst).mul (fm.comp measurable_snd)
  have mb (z : UnitSphere E×UnitSphere E) : ‖f z.1*f z.2‖ ≤ B*B := by
    rw [norm_mul]
    exact mul_le_mul (fb z.1) (fb z.2) (norm_nonneg _) B0
  have UI : Integrable U ν := by
    apply Integrable.of_bound (((capKernel_joint_measurable t).sub measurable_const).mul mm).aestronglyMeasurable
      ((1+‖q‖)*(B*B))
    apply ae_of_all
    intro z
    change ‖(capKernel t z.1 z.2-q)*(f z.1*f z.2)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul ((norm_sub_le _ _).trans
      (add_le_add_left (norm_capKernel_le_one t z.1 z.2) _)) (mb z) (by positivity) (by positivity)
  have VI : Integrable V ν := by
    apply Integrable.of_bound (Dm.mul mm).aestronglyMeasurable (B*B)
    apply ae_of_all
    intro z
    change ‖D z*(f z.1*f z.2)‖≤_
    have d : ‖D z‖≤1 := (err z).trans (by by_cases hz : z∈e <;> simp [hz])
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul d (mb z) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have HI : Integrable H ν := UV ▸ UI.add VI
  have fin := grid_double_integral σ code mc (fun i j => K i j-q) v
  change (∫ x, (∫ y, H (x,y) ∂σ) ∂σ)=_ at fin
  rw [←fin,←integral_prod H HI,UV,integral_add UI VI]
  have nonneg : 0≤q*Real.sqrt (squaredCapContraction n t)+Real.sqrt (ν.real e) :=
    add_nonneg (mul_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  calc
    _ ≤ ‖∫ z,U z ∂ν‖ + ‖∫ z,V z ∂ν‖ := norm_add_le _ _
    _ ≤ (q*Real.sqrt (squaredCapContraction n t))*((energyNorm σ f)^2) +
        Real.sqrt (ν.real e)*(energyNorm σ f)^2 := add_le_add cp ep
    _ = (q*Real.sqrt (squaredCapContraction n t)+Real.sqrt (ν.real e))*(energyNorm σ f)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left el2 nonneg

#print axioms grid_centered_cap_quadratic
end RobustFolkman.GeometricGap
