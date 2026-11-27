import GeometricSphereTransitive
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace RobustFolkman.GeometricGap
open MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem sphere_inner_square_integrable (a : UnitSphere E) (σ : Measure (UnitSphere E))
    [IsFiniteMeasure σ] : Integrable (fun u : UnitSphere E => (⟪a.val,u.val⟫_ℝ)^2) σ := by
  have m : Measurable (fun u : UnitSphere E => (⟪a.val,u.val⟫_ℝ)^2) :=
    ((continuous_const.inner (𝕜:=ℝ) continuous_subtype_val).pow 2).measurable
  refine Integrable.of_bound m.aestronglyMeasurable 1 ?_
  apply ae_of_all
  intro u
  have a1 : ‖a.val‖=1 := by simpa using a.property
  have u1 : ‖u.val‖=1 := by simpa using u.property
  have b := abs_real_inner_le_norm a.val u.val
  rw [a1,u1,mul_one] at b
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have z := pow_le_pow_left₀ (abs_nonneg _) b 2
  rwa [sq_abs,one_pow] at z

theorem sphere_inner_square_const (a b : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    (∫ u : UnitSphere E, (⟪a.val,u.val⟫_ℝ)^2 ∂σ) =
      ∫ u : UnitSphere E, (⟪b.val,u.val⟫_ℝ)^2 ∂σ := by
  intro σ
  obtain ⟨e,h,p⟩ := uniformSphere_transitive a b
  have z : b.val=e a.val := by rw [←h,sphereRotation_val]
  have q := p.integral_comp' (fun u => (⟪b.val,u.val⟫_ℝ)^2)
  simpa only [z,sphereRotation_val,e.inner_map_map] using q

/-- Exact second moment in every tangent direction under the uniform
sphere law. This is the isotropic input to the rotation coupling. -/
theorem sphere_inner_square_mean (a : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    (∫ u : UnitSphere E, (⟪a.val,u.val⟫_ℝ)^2 ∂σ) =
      1/(Module.finrank ℝ E:ℝ) := by
  intro σ
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let n := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  let U : Fin n→UnitSphere E := fun i => ⟨b i,by simpa using b.norm_eq_one i⟩
  let z := ∫ u : UnitSphere E, (⟪a.val,u.val⟫_ℝ)^2 ∂σ
  have f : (∫ u : UnitSphere E, ∑ i : Fin n, (⟪(U i).val,u.val⟫_ℝ)^2 ∂σ) =
      ∑ i, ∫ u : UnitSphere E, (⟪(U i).val,u.val⟫_ℝ)^2 ∂σ :=
    integral_finsetSum _ (fun i _ => sphere_inner_square_integrable (U i) σ)
  have q (u : UnitSphere E) : (∑ i : Fin n, (⟪(U i).val,u.val⟫_ℝ)^2)=1 := by
    change (∑ i : Fin n, (⟪b i,u.val⟫_ℝ)^2)=1
    rw [b.sum_sq_inner_right]
    norm_num [show ‖u.val‖=1 from by simpa using u.property]
  simp_rw [q] at f
  have c (i : Fin n) : (∫ u : UnitSphere E, (⟪(U i).val,u.val⟫_ℝ)^2 ∂σ) = z :=
    sphere_inner_square_const (U i) a
  simp only [integral_const,show σ.real Set.univ=1 from by simp [Measure.real],one_smul] at f
  rw [Finset.sum_congr rfl (fun i _ => c i)] at f
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at f
  have np : 0<(n:ℝ) := by exact_mod_cast Module.finrank_pos (R:=ℝ) (M:=E)
  change z=1/(n:ℝ)
  apply (eq_div_iff np.ne').2
  nlinarith only [f]

#print axioms sphere_inner_square_mean
end RobustFolkman.GeometricGap
