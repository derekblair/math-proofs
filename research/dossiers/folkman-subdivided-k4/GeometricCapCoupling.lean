import GeometricCapHeightMoment

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def capLaw (t : ℝ) (a : UnitSphere E) : Measure (UnitSphere E) :=
  condOn (uniformSphere (volume : Measure E)) (capPoints t a)

theorem capLaw_probability (t : ℝ) (t0 : -1<t) (t1 : t<1) (a : UnitSphere E) :
    IsProbabilityMeasure (capLaw t a) := by
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  exact condOn_probability σ _ (capPoints_both_positive t t0 t1 a).1.ne' (measure_ne_top σ _)

noncomputable def squaredCapContraction (n : ℕ) (t : ℝ) : ℝ :=
  4*t^2+Real.exp (3-2*((n:ℝ)/2)*t^2)+1/((n:ℝ)+2)

theorem plane_rotation_preserves_cap (t : ℝ) (a b : UnitSphere E)
    (R : E ≃ₗᵢ[ℝ] E) (h : R a.val=b.val) :
    MeasurePreserving (sphereRotation R) (capLaw t a) (capLaw t b) := by
  have rp := sphereRotation_volume R
  have u : sphereRotation R ⁻¹' capPoints t b=capPoints t a := by
    ext z
    change t≤⟪b.val,(sphereRotation R z).val⟫_ℝ ↔ t≤⟪a.val,z.val⟫_ℝ
    rw [←h,sphereRotation_val,R.inner_map_map]
  have v := conditional_transport (sphereRotation R) rp (capPoints t b) (capPoints_measurable t b)
  simpa only [u,capLaw] using v

/-- A coupling of the cap transition measures gives a dimension-
explicit bound on mean squared displacement. -/
theorem cap_coupling_squared_bound (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (large : 3≤(n:ℝ)/2)
    (dense : 1≤4*((n:ℝ)/2)*t^2) (a b : UnitSphere E) :
    ∃ R : E ≃ₗᵢ[ℝ] E,
      MeasurePreserving (sphereRotation R) (capLaw t a) (capLaw t b) ∧
      (∫ z : UnitSphere E, ‖R z.val-z.val‖^2 ∂capLaw t a)≤
        ‖b.val-a.val‖^2*squaredCapContraction n t := by
  have an : ‖a.val‖=1 := by simpa using a.property
  have bn : ‖b.val‖=1 := by simpa using b.property
  obtain ⟨v,R,vn,ov,hR,h⟩ := sphere_plane_coupling (by omega : 2≤Module.finrank ℝ E) a.val b.val an bn
  let V : UnitSphere E := ⟨v,by simpa using vn⟩
  let μ := capLaw t a
  letI : IsProbabilityMeasure μ := capLaw_probability t (by linarith only [tp]) (by linarith only [ts]) a
  let F := fun z : UnitSphere E => (⟪a.val,z.val⟫_ℝ)^2
  let G := fun z : UnitSphere E => (⟪V.val,z.val⟫_ℝ)^2
  have fi : Integrable F μ := sphere_inner_square_integrable a μ
  have gi : Integrable G μ := sphere_inner_square_integrable V μ
  have fa := conditional_cap_height_second n dim t tp ts large dense a
  have ga := cap_tangent_second_moment (by omega : 3≤Module.finrank ℝ E) t
    (by linarith only [tp]) (by linarith only [ts]) a V ov
  have d : (Module.finrank ℝ E:ℝ)-1=(n:ℝ)+2 := by rw [dim]; push_cast; ring
  rw [d] at ga
  refine ⟨R,plane_rotation_preserves_cap t a b R hR,?_⟩
  have h' (z : UnitSphere E) : ‖R z.val-z.val‖^2=‖b.val-a.val‖^2*(F z+G z) := h z.val
  simp_rw [h']
  rw [integral_const_mul,integral_add fi gi]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact add_le_add fa ga

#print axioms cap_coupling_squared_bound
end RobustFolkman.GeometricGap
