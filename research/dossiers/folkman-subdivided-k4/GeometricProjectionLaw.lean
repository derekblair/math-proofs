import GeometricSphericalProjection

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

noncomputable def reciprocalRadial (n : ℕ) : ℝ → ℝ≥0∞ :=
  (Ioo (0:ℝ) 1).indicator (fun r => (ENNReal.ofReal (r^n))⁻¹)

theorem reciprocalRadial_measurable (n : ℕ) : Measurable (reciprocalRadial n) :=
  ((measurable_id.pow_const _).ennreal_ofReal.inv).indicator measurableSet_Ioo

theorem reciprocalRadial_integral (n : ℕ) :
    (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^n)*reciprocalRadial n r) = 1 := by
  have con : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^n)*reciprocalRadial n r) =
      ∫⁻ r in Ioi (0:ℝ), (Ioo (0:ℝ) 1).indicator (fun _ => (1:ℝ≥0∞)) r := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have rp : 0<r := hr
    dsimp only
    by_cases b : r∈Ioo (0:ℝ) 1
    · simp only [reciprocalRadial,indicator_of_mem b]
      exact ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (pow_pos rp _)).ne' ENNReal.ofReal_ne_top
    · simp [reciprocalRadial,indicator_of_notMem b]
  rw [con,lintegral_indicator measurableSet_Ioo,Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (fun r hr => hr.1),setLIntegral_const]
  simp [Real.volume_Ioo]

/-- Exact law of the coordinate projection of a point sampled from
the normalized Haar sphere in an orthogonal direct sum. -/
theorem spherical_projection_probability (m : ℕ)
    (dim : Module.finrank ℝ W=m+2) (g : (I→ℝ)→ℝ≥0∞) (gm : Measurable g) :
    (∫⁻ x : UnitSphere (SphereAmbient I W), g (ofLp (ofLp x.val).1)
      ∂uniformSphere (volume : Measure (SphereAmbient I W))) =
      (∫⁻ u in (projectionBall : Set (I→ℝ)), projectionFactor m u*g u) /
        (∫⁻ u in (projectionBall : Set (I→ℝ)), projectionFactor m u) := by
  let μ := (volume : Measure (SphereAmbient I W))
  let ω := (volume : Measure W)
  let a := ω.toSphere univ
  let b := ∫⁻ u in (projectionBall : Set (I→ℝ)), projectionFactor m u
  let c := ∫⁻ u in (projectionBall : Set (I→ℝ)), projectionFactor m u*g u
  let h := reciprocalRadial (Fintype.card I+m+1)
  have hm : Measurable h := reciprocalRadial_measurable _
  have hr : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Fintype.card I+m+1))*h r) = 1 :=
    reciprocalRadial_integral _
  have h0 : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Fintype.card I+m+1))*h r)≠0 := by
    rw [hr]; exact one_ne_zero
  have ht : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Fintype.card I+m+1))*h r)≠∞ := by
    rw [hr]; exact ENNReal.one_ne_top
  have res := spherical_projection_unnormalized (W:=W) m dim g gm h hm h0 ht
  have normer := spherical_projection_unnormalized (W:=W) m dim
    (fun _ : I→ℝ => (1:ℝ≥0∞)) measurable_const h hm h0 ht
  simp only [lintegral_const,one_mul,mul_one] at normer
  have ac : a≠0 := by
    intro e
    exact ω.toSphere_ne_zero (Measure.measure_univ_eq_zero.mp e)
  have atp : a≠∞ := measure_ne_top _ _
  unfold uniformSphere
  rw [lintegral_smul_measure,smul_eq_mul,res,normer]
  change (a*b)⁻¹*(a*c)=c/b
  rw [← ENNReal.div_eq_inv_mul,ENNReal.mul_div_mul_left _ _ ac atp]

#print axioms spherical_projection_probability
end RobustFolkman.GeometricGap
