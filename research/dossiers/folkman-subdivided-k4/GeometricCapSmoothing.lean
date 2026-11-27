import GeometricSphericalStrip

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem cap_kernel_disagreement (t : ℝ) (a b z : UnitSphere E)
    (h : capKernel t a z≠capKernel t b z) :
    z∈ rootHeightStrip a (t-dist a b) (t+dist a b) := by
  have h0 : ‖z.val‖=1 := by simpa using z.property
  have hb : |⟪b.val,z.val⟫_ℝ-⟪a.val,z.val⟫_ℝ|≤dist a b := by
    rw [←inner_sub_left]
    have H := abs_real_inner_le_norm (b.val-a.val) z.val
    rw [h0,mul_one,norm_sub_rev] at H
    change _≤dist a.val b.val
    rw [dist_eq_norm]
    exact H
  have neq : ¬ (t≤⟪a.val,z.val⟫_ℝ ↔ t≤⟪b.val,z.val⟫_ℝ) := by
    intro hh
    have e : z∈capPoints t a ↔ z∈capPoints t b := hh
    apply h
    unfold capKernel
    by_cases h' : z∈capPoints t a
    · rw [indicator_of_mem h',indicator_of_mem (e.1 h')]
    · rw [indicator_of_notMem h',indicator_of_notMem (fun v => h' (e.2 v))]
  exact threshold_disagreement_in_strip _ _ _ _ hb neq

/-- Cap averaging regularizes every bounded measurable function to a
Lipschitz function. The one-step smoothing gives an alternative to
constructing a dense Lipschitz subspace of L². -/
theorem capAverage_smoothing (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (a : UnitSphere E)
    (f : UnitSphere E→ℝ) (fm : Measurable f) (B : ℝ) (B0 : 0≤B) (bd : ∀ x, ‖f x‖≤B) :
    ∃ L : ℝ≥0, LipschitzWith L (capAverage t f) := by
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let Z := (sliceMass ((n:ℝ)/2) (-1) 1).toReal
  let q := σ.real (capPoints t a)
  have q0 : 0≤q := ENNReal.toReal_nonneg
  let L := 4*B+(B*q⁻¹)*(2/Z)
  have L0 : 0≤L := by dsimp [L]; positivity
  refine ⟨⟨L,L0⟩,LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  change dist (capAverage t f x) (capAverage t f y)≤ L*dist x y
  let δ := dist x y
  have δ0 : 0≤δ := dist_nonneg
  have t0 : -1<t := by linarith only [tp]
  have t1 : t<1 := by linarith only [ts]
  by_cases small : δ≤1/2
  · let U := rootHeightStrip x (t-δ) (t+δ)
    have Um : MeasurableSet U := rootHeightStrip_measurable x _ _
    have len : σ.real U≤2*δ/Z := by
      have h := root_strip_real_bound n dim x (t-δ) (t+δ)
        (by linarith only [tp,small]) (by linarith only [ts,small]) (by linarith only [δ0])
      change σ.real U≤(t+δ-(t-δ))/Z at h
      convert h using 1 <;> ring
    let X := fun z => capKernel t x z*f z
    let Y := fun z => capKernel t y z*f z
    have XI (u : UnitSphere E) : Integrable (fun z => capKernel t u z*f z) σ := by
      have km : Measurable (fun z => capKernel t u z) := measurable_const.indicator (capPoints_measurable t u)
      apply Integrable.of_bound (km.mul fm).aestronglyMeasurable B
      apply ae_of_all
      intro z
      change ‖capKernel t u z*f z‖≤B
      rw [norm_mul]
      exact (mul_le_mul (norm_capKernel_le_one t u z) (bd z) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have I : Integrable (U.indicator (fun _ => B)) σ := (integrable_const _).indicator Um
    have val (z : UnitSphere E) : ‖X z-Y z‖≤U.indicator (fun _ => B) z := by
      by_cases eq : capKernel t x z=capKernel t y z
      · simp only [X,Y,eq,sub_self,norm_zero]
        exact indicator_nonneg (fun _ _ => B0) _
      · have hu : z∈U := cap_kernel_disagreement t x y z eq
        rw [indicator_of_mem hu]
        change ‖capKernel t x z*f z-capKernel t y z*f z‖≤B
        rw [←sub_mul,norm_mul]
        have h : ‖capKernel t x z-capKernel t y z‖≤1 := by
          unfold capKernel
          by_cases A : z∈capPoints t x <;> by_cases C : z∈capPoints t y <;>
            simp [indicator_of_mem,indicator_of_notMem,A,C]
        exact (mul_le_mul h (bd z) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have v := norm_integral_le_of_norm_le (μ:=σ) I (ae_of_all σ val)
    rw [integral_indicator Um,setIntegral_const,smul_eq_mul] at v
    rw [dist_eq_norm,capAverage_as_kernel t f a x,capAverage_as_kernel t f a y,←mul_sub]
    change ‖q⁻¹*((∫ z, X z ∂σ)-(∫ z, Y z ∂σ))‖≤L*δ
    rw [←integral_sub (XI x) (XI y),norm_mul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr q0)]
    calc
      _ ≤ q⁻¹*(σ.real U*B) := mul_le_mul_of_nonneg_left v (inv_nonneg.mpr q0)
      _ ≤ q⁻¹*((2*δ/Z)*B) := by gcongr
      _ = ((B*q⁻¹)*(2/Z))*δ := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ δ0
        dsimp [L]
        linarith only [B0]
  · have v := norm_sub_le (capAverage t f x) (capAverage t f y)
    have vx := capAverage_bound t t0 t1 f B bd x
    have vy := capAverage_bound t t0 t1 f B bd y
    rw [dist_eq_norm]
    have r : 4*B*(1/2:ℝ)≤4*B*δ :=
      mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge small)) (by positivity)
    have e : 4*B*δ≤L*δ := by apply mul_le_mul_of_nonneg_right _ δ0; dsimp [L]; apply le_add_of_nonneg_right; positivity
    linarith only [v,vx,vy,r,e]

#print axioms capAverage_smoothing
end RobustFolkman.GeometricGap
