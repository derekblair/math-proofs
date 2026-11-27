import GeometricActualSampleCut
import GeometricMatrixReindex

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset WithLp
open scoped ENNReal BigOperators Matrix.Norms.L2Operator InnerProductSpace
variable {J E : Type*} [Fintype J] [DecidableEq J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem centeredSample_pointGraph (t q : ℝ) (x : J→UnitSphere E) :
    centeredSample (capKernel t) q x =
      linkAdjMatrix (pointGraph t x)-Matrix.of (fun i j : J => if i=j then 0 else q) := by
  ext i j
  by_cases ij : i=j
  · subst j; simp [centeredSample,linkAdjMatrix]
  · have h := pointGraph_pair t x ij
    simp [centeredSample,linkAdjMatrix,ij,h,capKernel_eq_ite]

theorem measurable_bad_sphere_norm (t q b : ℝ) :
    MeasurableSet {x : J→UnitSphere E | b<‖centeredSample (capKernel t) q x‖} := by
  simp_rw [centeredSample_pointGraph]
  exact measurable_pointGraph_pred t (fun g => b<‖linkAdjMatrix g -
    Matrix.of (fun i j : J => if i=j then 0 else q)‖)

theorem spherical_ambient_sample_tail (n N : ℕ) (dim : Module.finrank ℝ E=n+3)
    (labels : Fintype.card J=N+1) (t : ℝ) (tp : 0<t) (ts : t≤1/8) (a : UnitSphere E)
    (large : 3≤(n:ℝ)/2) (dense : 1≤4*((n:ℝ)/2)*t^2)
    (gap : Real.sqrt (squaredCapContraction n t)≤1/200) :
    let σ := uniformSphere (volume : Measure E)
    let q := σ.real (capPoints t a)
    let D := Fintype.card (GridCode (n+3) (gridResolution n 20))
    let L := N+1
    100≤(L:ℝ)*q →
    (Measure.pi (fun _ : J => σ)).real {x | 4*(L:ℝ)*q/50<‖centeredSample (capKernel t) q x‖}
      ≤ ((2*(D:ℝ)+3*(L:ℝ))*Real.exp (-(L:ℝ)*q/1000000))/(q/100) +
        (L:ℝ)*Real.exp (-(L:ℝ)*q/1000) := by
  classical
  intro σ q D L hq
  let I := Fin (n+3)
  let b := (stdOrthonormalBasis ℝ E).reindex (finCongr dim)
  let f : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ I := b.repr
  letI : Nontrivial (EuclideanSpace ℝ I) := f.injective.nontrivial
  let τ := uniformSphere (volume : Measure (EuclideanSpace ℝ I))
  let a' := sphereTransport f a
  have T := sphereTransport_volume f
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  letI : IsProbabilityMeasure τ := uniformSphere_isProbability _
  let e : J ≃ Fin L := Fintype.equivFinOfCardEq labels
  have all := measurePreserving_pi (fun _ : J => σ) (fun _ => τ) (fun _ => T)
  have re := measurePreserving_piCongrLeft (fun _ : Fin L => τ) e
  let φ := fun x : J→UnitSphere E => fun i : Fin L => sphereTransport f (x (e.symm i))
  have law : MeasurePreserving φ (Measure.pi fun _ : J => σ) (Measure.pi fun _ : Fin L => τ) := by
    convert re.comp all using 1
    funext x i
    change sphereTransport f (x (e.symm i))=
      MeasurableEquiv.piCongrLeft (fun _ => GridSphere (n+3)) e (fun j => sphereTransport f (x j)) i
    have h := MeasurableEquiv.piCongrLeft_apply_apply e (β:=fun _ => GridSphere (n+3))
      (fun j => sphereTransport f (x j)) (e.symm i)
    rw [e.apply_symm_apply] at h
    exact h.symm
  have mm (x y : UnitSphere E) :
      capKernel t (sphereTransport f x) (sphereTransport f y)=capKernel t x y := by
    simp only [capKernel_eq_ite,sphereTransport_val,f.inner_map_map]
  have cap : (sphereTransport f) ⁻¹' capPoints t a' = capPoints t a := by
    ext x
    change t≤⟪(sphereTransport f a).val,(sphereTransport f x).val⟫_ℝ ↔ t≤⟪a.val,x.val⟫_ℝ
    simp only [sphereTransport_val,f.inner_map_map]
  have qeq : τ.real (capPoints t a')=q := by
    have h := T.measure_preimage (capPoints_measurable t a').nullMeasurableSet
    rw [cap] at h
    exact congrArg ENNReal.toReal h.symm
  have eq (x : J→UnitSphere E) :
      centeredSample (capKernel t) q (φ x) =
        (centeredSample (capKernel t) q x).submatrix e.symm e.symm := by
    ext i j
    by_cases h : i=j
    · subst j; simp [centeredSample]
    · simp [centeredSample,Matrix.submatrix_apply,h,(e.symm.injective.ne h),φ,mm]
  let B := {x : Fin L→GridSphere (n+3) | 4*(L:ℝ)*q/50<‖centeredSample (capKernel t) q x‖}
  have bm : MeasurableSet B := measurable_bad_sphere_norm t q _
  have pre : φ ⁻¹' B={x : J→UnitSphere E | 4*(L:ℝ)*q/50<‖centeredSample (capKernel t) q x‖} := by
    ext x
    change (4*(L:ℝ)*q/50<‖centeredSample (capKernel t) q (φ x)‖) ↔ _
    rw [eq,rectangular_reindex_norm]
    rfl
  unfold Measure.real
  rw [←pre,law.measure_preimage bm.nullMeasurableSet]
  have h := spherical_actual_sample_tail n N t tp ts a' large dense gap
  change 100≤(L:ℝ)*τ.real (capPoints t a') → _ at h
  rw [qeq] at h
  exact h hq

#print axioms spherical_ambient_sample_tail
end RobustFolkman.GeometricGap
