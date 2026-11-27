import GeometricTrianglePacking

namespace RobustFolkman.GeometricGap
open MeasureTheory Finset Set
open scoped ENNReal
variable {V E : Type*} [DecidableEq V] [Fintype V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem triangle_root_mass (t : ℝ) (a b c : V) (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    let σ := uniformSphere (volume : Measure E)
    (patternMass (E:=E) triangleCon t).toReal = ((σ.prod (σ.prod σ)) (triangleFromRoot t)).toReal := by
  classical
  intro σ
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let l : (Fin 2⊕Unit)↪V := ⟨tripleLabel b c a,tripleLabel_injective bc ab.symm ac.symm⟩
  let F := fun x : V→UnitSphere E => packTri (x∘l)
  have pres : MeasurePreserving F (Measure.pi fun _ : V => σ) (σ.prod (σ.prod σ)) :=
    (packTri_measurePreserving σ).comp (pi_embedding_measurePreserving σ l)
  have sub : F ⁻¹' triangleFromRoot t =
      {x | ({a,b,c}:Finset V).powersetCard 2 ⊆ pointGraph t x} := by
    ext x
    exact (triangle_event_root t a b c ab ac bc x).symm
  have mp := pres.measure_preimage (triangleFromRoot_measurable (E:=E) t).nullMeasurableSet
  rw [sub] at mp
  rw [← triangle_moment_exact (V:=V) (E:=E) t {a,b,c}
    (Finset.card_eq_three.mpr ⟨a,b,c,ab,ac,bc,rfl⟩)]
  unfold triangleIndicator
  rw [mean_event_of_host]
  exact congrArg ENNReal.toReal mp

theorem root_overlap_explicit (t : ℝ) (r : Tuple5 V) (inj : Function.Injective (tupleLabel r)) :
    Moment.mean (sphericalHostWeight (E:=E) t)
      (fun g => triangleIndicator g {r.2.2.2.2,r.2.2.1,r.2.2.2.1} *
        triangleIndicator g {r.2.2.2.2,r.1,r.2.1}) =
      ((patternMass (E:=E) triangleCon t).toReal)^2 := by
  classical
  rcases r with ⟨u,v,x,y,z⟩
  obtain ⟨uv,xy,zx,zy,ux,uy,vx,vy,uz,vz⟩ := tupleLabel_distinct _ inj
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let l : Five↪V := ⟨tupleLabel (u,v,x,y,z),inj⟩
  let F := fun a : V→UnitSphere E => packRootedTwo (a∘l)
  have pres : MeasurePreserving F (Measure.pi fun _ : V => σ)
      (σ.prod ((σ.prod σ).prod (σ.prod σ))) :=
    (packRootedTwo_measurePreserving σ).comp (pi_embedding_measurePreserving σ l)
  let P : EdgeGraph V→Prop := fun g =>
    ({z,x,y}:Finset V).powersetCard 2 ⊆ g ∧ ({z,u,v}:Finset V).powersetCard 2 ⊆ g
  have sub : F ⁻¹' twoTrianglesFromRoot t = {a | P (pointGraph t a)} := by
    ext a
    change (F a).2.1∈triangleAt t (F a).1 ∧ (F a).2.2∈triangleAt t (F a).1 ↔ _
    change (a z,a x,a y)∈triangleFromRoot t ∧ (a z,a u,a v)∈triangleFromRoot t ↔ _
    exact and_congr (triangle_event_root t z x y zx zy xy a).symm
      (triangle_event_root t z u v uz.symm vz.symm uv a).symm
  have mp := pres.measure_preimage (twoTrianglesFromRoot_measurable (E:=E) t).nullMeasurableSet
  rw [sub] at mp
  have law := shared_root_triangle_probability t (E:=E)
  obtain ⟨a⟩ := (NormedSpace.sphere_nonempty_rclike (𝕜:=ℝ) (E:=E) (r:=1) (by norm_num))
  have ep := law a
  have fm (g : EdgeGraph V) :
      triangleIndicator (K:=ℝ) g {z,x,y} * triangleIndicator g {z,u,v} =
        if P g then 1 else 0 := by
    simp only [triangleIndicator,P]
    split <;> split <;> simp_all
  simp_rw [fm]
  rw [mean_event_of_host,mp]
  have e := congrArg ENNReal.toReal ep
  rw [ENNReal.toReal_pow] at e
  rw [e]
  rw [triangle_root_mass (E:=E) t z x y zx zy xy]

#print axioms root_overlap_explicit
end RobustFolkman.GeometricGap
