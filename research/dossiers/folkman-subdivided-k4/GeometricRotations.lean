import GeometricUniformSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace RobustFolkman
open MeasureTheory Set
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

noncomputable def sphereRotation (e : E ≃ₗᵢ[ℝ] E) : UnitSphere E ≃ᵐ UnitSphere E :=
  (e.toHomeomorph.subtype (p:=fun x => x∈Metric.sphere (0:E) 1)
    (q:=fun x => x∈Metric.sphere (0:E) 1) (fun x => by simp)).toMeasurableEquiv

theorem sphereRotation_val (e : E ≃ₗᵢ[ℝ] E) (x : UnitSphere E) :
    (sphereRotation e x : E)=e x := rfl

def coneOf (s : Set (UnitSphere E)) : Set E :=
  Ioo (0:ℝ) 1 • ((↑) '' s)

theorem cone_rotation (e : E ≃ₗᵢ[ℝ] E) (s : Set (UnitSphere E)) :
    e '' coneOf s = coneOf ((sphereRotation e) '' s) := by
  ext w
  constructor
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨r,hr,x,hx,ux⟩ := Set.mem_smul.mp hu
    obtain ⟨z,hz,rfl⟩ := hx
    refine Set.mem_smul.mpr ⟨r,hr,(sphereRotation e z : E),⟨sphereRotation e z,⟨z,hz,rfl⟩,rfl⟩,?_⟩
    rw [sphereRotation_val,← e.map_smul,ux]
  · intro hw
    obtain ⟨r,hr,x,hx,wx⟩ := Set.mem_smul.mp hw
    obtain ⟨z,⟨u,hu,rfl⟩,rfl⟩ := hx
    refine ⟨r • (u:E),Set.mem_smul.mpr ⟨r,hr,(u:E),⟨u,hu,rfl⟩,rfl⟩,?_⟩
    simpa only [e.map_smul,sphereRotation_val] using wx

theorem sphereRotation_measurePreserving (μ : Measure E) (e : E ≃ₗᵢ[ℝ] E)
    (pres : MeasurePreserving e μ μ) :
    MeasurePreserving (sphereRotation e) (uniformSphere μ) (uniformSphere μ) := by
  let f := sphereRotation e
  have amb (S : Set E) : μ (e '' S)=μ S := by
    have h := congrArg (fun m : Measure E => m (e '' S)) pres.map_eq
    change (Measure.map e.toMeasurableEquiv μ) (e '' S)=μ (e '' S) at h
    rw [e.toMeasurableEquiv.measurableEmbedding.map_apply]
      at h
    have z : (⇑e.toMeasurableEquiv) ⁻¹' (e '' S)=S := e.injective.preimage_image S
    rw [z] at h
    exact h.symm
  have img (s : Set (UnitSphere E)) (hs : MeasurableSet s) :
      μ.toSphere (f '' s)=μ.toSphere s := by
    rw [μ.toSphere_apply' (f.measurableSet_image.mpr hs), μ.toSphere_apply' hs]
    change _ * μ (coneOf (f '' s)) = _ * μ (coneOf s)
    rw [←cone_rotation,amb]
  refine ⟨f.measurable,?_⟩
  ext s hs
  rw [f.measurableEmbedding.map_apply]
  have z := img (f ⁻¹' s) (f.measurable hs)
  rw [f.surjective.image_preimage] at z
  rw [uniformSphere,Measure.smul_apply,Measure.smul_apply,z]

theorem sphereRotation_volume (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereRotation e) (uniformSphere (volume : Measure E))
      (uniformSphere (volume : Measure E)) :=
  sphereRotation_measurePreserving volume e e.measurePreserving

#print axioms sphereRotation_volume
end RobustFolkman
