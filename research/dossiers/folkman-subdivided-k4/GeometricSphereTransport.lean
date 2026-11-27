import GeometricConeRatio

namespace RobustFolkman
open MeasureTheory Set
open scoped Pointwise ENNReal
variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

noncomputable def sphereTransport (e : E ≃ₗᵢ[ℝ] F) : UnitSphere E ≃ᵐ UnitSphere F :=
  (e.toHomeomorph.subtype (p:=fun x => x∈Metric.sphere (0:E) 1)
    (q:=fun x => x∈Metric.sphere (0:F) 1) (fun x => by simp)).toMeasurableEquiv

theorem sphereTransport_val (e : E ≃ₗᵢ[ℝ] F) (x : UnitSphere E) :
    (sphereTransport e x : F)=e x := rfl

theorem cone_transport (e : E ≃ₗᵢ[ℝ] F) (s : Set (UnitSphere E)) :
    e '' coneOf s = coneOf ((sphereTransport e) '' s) := by
  ext w
  constructor
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨r,hr,x,hx,ux⟩ := Set.mem_smul.mp hu
    obtain ⟨z,hz,rfl⟩ := hx
    refine Set.mem_smul.mpr ⟨r,hr,(sphereTransport e z : F),⟨sphereTransport e z,⟨z,hz,rfl⟩,rfl⟩,?_⟩
    rw [sphereTransport_val,← e.map_smul,ux]
  · intro hw
    obtain ⟨r,hr,x,hx,wx⟩ := Set.mem_smul.mp hw
    obtain ⟨z,⟨u,hu,rfl⟩,rfl⟩ := hx
    refine ⟨r • (u:E),Set.mem_smul.mpr ⟨r,hr,(u:E),⟨u,hu,rfl⟩,rfl⟩,?_⟩
    simpa only [e.map_smul,sphereTransport_val] using wx

/-- Normalized spherical volume is invariant across isometric ambient
types, not just under a rotation on a fixed type. -/
theorem sphereTransport_volume [Nontrivial E] [Nontrivial F] (e : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving (sphereTransport e)
      (uniformSphere (volume : Measure E)) (uniformSphere (volume : Measure F)) := by
  let μ := (volume : Measure E)
  let ν := (volume : Measure F)
  let f := sphereTransport e
  have v := e.measurePreserving
  have amb (s : Set E) : ν (e '' s)=μ s := by
    have h := congrArg (fun m : Measure F => m (e '' s)) v.map_eq
    change (Measure.map e.toMeasurableEquiv μ) (e '' s)=ν (e '' s) at h
    rw [e.toMeasurableEquiv.measurableEmbedding.map_apply] at h
    have z : (⇑e.toMeasurableEquiv) ⁻¹' (e '' s)=s := e.injective.preimage_image s
    rw [z] at h
    exact h.symm
  have ball : e '' Metric.ball (0:E) 1 = Metric.ball (0:F) 1 := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa [Metric.mem_ball,dist_zero_right] using hy
    · intro hx
      refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
      simpa [Metric.mem_ball,dist_zero_right] using hx
  have eqBall := amb (Metric.ball (0:E) 1)
  rw [ball] at eqBall
  refine ⟨f.measurable,?_⟩
  ext s hs
  rw [f.measurableEmbedding.map_apply, uniformSphere_cone_ratio _ _ (f.measurable hs),
    uniformSphere_cone_ratio _ _ hs]
  have img : ν (coneOf s) = μ (coneOf (f ⁻¹' s)) := by
    have h := amb (coneOf (f ⁻¹' s))
    rw [cone_transport, f.surjective.image_preimage] at h
    exact h
  rw [← img,← eqBall]

#print axioms sphereTransport_volume
end RobustFolkman
