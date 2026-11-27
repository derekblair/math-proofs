import GeometricCapLipschitz
import Mathlib.MeasureTheory.Integral.Prod

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def capKernel (t : ℝ) (x y : UnitSphere E) : ℝ :=
  (capPoints t x).indicator (fun _ => 1) y

theorem capKernel_joint_measurable (t : ℝ) :
    Measurable (fun p : UnitSphere E×UnitSphere E => capKernel t p.1 p.2) := by
  have m : MeasurableSet {p : UnitSphere E×UnitSphere E | t≤⟪p.1.val,p.2.val⟫_ℝ} :=
    measurableSet_le measurable_const
      ((continuous_subtype_val.comp continuous_fst).inner (𝕜:=ℝ)
        (continuous_subtype_val.comp continuous_snd)).measurable
  exact measurable_const.indicator m

theorem capKernel_symm (t : ℝ) (x y : UnitSphere E) : capKernel t x y=capKernel t y x := by
  have hxy : x∈capPoints t y ↔ y∈capPoints t x := by
    change t≤⟪y.val,x.val⟫_ℝ ↔ t≤⟪x.val,y.val⟫_ℝ
    rw [real_inner_comm x.val y.val]
  by_cases h : y∈capPoints t x
  · simp [capKernel,indicator_of_mem h,indicator_of_mem (hxy.2 h)]
  · simp [capKernel,indicator_of_notMem h,indicator_of_notMem (fun z => h (hxy.1 z))]

theorem norm_capKernel_le_one (t : ℝ) (x y : UnitSphere E) : ‖capKernel t x y‖≤1 := by
  unfold capKernel
  by_cases h : y∈capPoints t x <;> simp [indicator_of_mem,indicator_of_notMem,h]

theorem capAverage_as_kernel (t : ℝ) (f : UnitSphere E→ℝ) (a x : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    capAverage t f x = (σ.real (capPoints t a))⁻¹ * ∫ y, capKernel t x y * f y ∂σ := by
  intro σ
  have eq := capPoints_mass_root_constant t x a
  unfold capAverage capLaw condOn
  rw [integral_smul_measure, ←integral_indicator (capPoints_measurable t x),
    ENNReal.toReal_inv,smul_eq_mul]
  change (σ (capPoints t x)).toReal⁻¹ * _ = _
  rw [eq]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro y
  by_cases h : y∈capPoints t x <;> simp [capKernel,indicator_of_mem,indicator_of_notMem,h]

theorem capAverage_symmetry_bounded (t : ℝ) (a : UnitSphere E)
    (f g : UnitSphere E→ℝ) (fm : Measurable f) (gm : Measurable g)
    (F G : ℝ) (F0 : 0≤F) (G0 : 0≤G)
    (fB : ∀ x, ‖f x‖≤F) (gB : ∀ x, ‖g x‖≤G) :
    let σ := uniformSphere (volume : Measure E)
    (∫ x, f x*capAverage t g x ∂σ) = ∫ x, capAverage t f x*g x ∂σ := by
  intro σ
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let H := fun p : UnitSphere E×UnitSphere E => capKernel t p.1 p.2 * (f p.1*g p.2)
  have HM : Measurable H := (capKernel_joint_measurable t).mul
    ((fm.comp measurable_fst).mul (gm.comp measurable_snd))
  have i : Integrable H (σ.prod σ) := by
    apply Integrable.of_bound HM.aestronglyMeasurable (F*G)
    apply ae_of_all
    intro p
    change ‖capKernel t p.1 p.2 * (f p.1*g p.2)‖≤F*G
    rw [norm_mul,norm_mul]
    have fg := mul_le_mul (fB p.1) (gB p.2) (norm_nonneg _) F0
    have k := norm_capKernel_le_one t p.1 p.2
    exact (mul_le_mul k fg (by positivity) (by norm_num)).trans_eq (one_mul _)
  have FI := integral_prod H i
  have GI := integral_prod_symm H i
  let q := (σ.real (capPoints t a))⁻¹
  have X (x : UnitSphere E) :
      (∫ y, H (x,y) ∂σ)=f x*(∫ y, capKernel t x y*g y ∂σ) := by
    simp_rw [H,show ∀ b c d : ℝ,b*(c*d)=c*(b*d) from fun b c d => by ring,
      integral_const_mul]
  have Y (y : UnitSphere E) :
      (∫ x, H (x,y) ∂σ)=(∫ x, capKernel t y x*f x ∂σ)*g y := by
    simp_rw [H,capKernel_symm t _ y,←mul_assoc,integral_mul_const]
  simp_rw [X] at FI
  simp_rw [Y] at GI
  have hf (x : UnitSphere E) : capAverage t f x=q*∫ y, capKernel t x y*f y ∂σ :=
    capAverage_as_kernel t f a x
  have hg (x : UnitSphere E) : capAverage t g x=q*∫ y, capKernel t x y*g y ∂σ :=
    capAverage_as_kernel t g a x
  -- Arrange the equal product-space integrals without commuting the two variables.
  have l : (∫ x, f x*capAverage t g x ∂σ)=q*∫ p, H p ∂(σ.prod σ) := by
    simp_rw [hg,show ∀ u v : ℝ,u*(q*v)=q*(u*v) from fun u v => by ring,integral_const_mul]
    rw [FI]
  have r : (∫ x, capAverage t f x*g x ∂σ)=q*∫ p, H p ∂(σ.prod σ) := by
    simp_rw [hf,mul_assoc,integral_const_mul]
    rw [GI]
  exact l.trans r.symm

#print axioms capAverage_symmetry_bounded
end RobustFolkman.GeometricGap
