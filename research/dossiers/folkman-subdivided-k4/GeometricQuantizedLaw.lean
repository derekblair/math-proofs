import GeometricGridRowMass
import GeometricKernelBernoulli
import GeometricGridResolution

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Matrix WithLp
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

noncomputable def gridLaw {d m : ℕ} (σ : Measure (GridSphere d)) :
    Measure (GridCode d m) := Measure.map (gridCode d m) σ

theorem gridLaw_preserving {d m : ℕ} (σ : Measure (GridSphere d)) :
    MeasurePreserving (gridCode d m) σ (gridLaw (m:=m) σ) :=
  ⟨gridCode_measurable d m,rfl⟩

instance gridLaw_probability {d m : ℕ} (σ : Measure (GridSphere d)) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (gridLaw (m:=m) σ) :=
  by
  constructor
  rw [gridLaw,Measure.map_apply (gridCode_measurable d m) MeasurableSet.univ]
  simp

theorem gridLaw_atom {d m : ℕ} (σ : Measure (GridSphere d)) (j : GridCode d m) :
    (gridLaw σ).real {j}=σ.real (gridCode d m ⁻¹' {j}) := by
  unfold Measure.real gridLaw
  rw [Measure.map_apply (gridCode_measurable d m) (measurableSet_singleton j)]

theorem gridSample_preserving {J : Type*} [Fintype J] {d m : ℕ}
    (σ : Measure (GridSphere d)) [IsProbabilityMeasure σ] :
    MeasurePreserving (fun x : J→GridSphere d => fun i => gridCode d m (x i))
      (Measure.pi (fun _ : J => σ)) (Measure.pi (fun _ : J => gridLaw (m:=m) σ)) :=
  measurePreserving_pi _ _ (fun _ => gridLaw_preserving σ)

theorem gridLaw_mass_total {d m : ℕ} (σ : Measure (GridSphere d)) [IsProbabilityMeasure σ] :
    ∑ j : GridCode d m, (gridLaw σ).real {j}=1 := by
  let ν := gridLaw (m:=m) σ
  change ∑ j : GridCode d m, (ν {j}).toReal=1
  rw [←ENNReal.toReal_sum (fun j _ => measure_ne_top ν {j}),
    sum_measure_singleton,Finset.coe_univ,measure_univ,ENNReal.toReal_one]

theorem quantized_grid_feature_bound (n m : ℕ)
    [Nontrivial (EuclideanSpace ℝ (Fin (n+3)))]
    (mp : 0<m) (t : ℝ) (a : GridSphere (n+3))
    (lo : -1≤t-2*(Real.sqrt ((n+3:ℕ):ℝ)/(m:ℝ)))
    (hi : t+2*(Real.sqrt ((n+3:ℕ):ℝ)/(m:ℝ))≤1) :
    let d := n+3
    let δ := 2*(Real.sqrt (d:ℝ)/(m:ℝ))
    let σ := uniformSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))
    let Z := (sliceMass ((n:ℝ)/2) (-1) 1).toReal
    let q := σ.real (capPoints t a)
    let p := fun j : GridCode d m => (gridLaw σ).real {j}
    let K := fun i j => quantizedCapKernel t a i j-q
    ∀ i, ∑ j,(kernelFeature K p i j)^2 ≤ q+2*δ/Z+q^2 := by
  classical
  intro d δ σ Z q p K i
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  have bs (i j : GridCode d m) :
      quantizedCapKernel t a i j=0 ∨ quantizedCapKernel t a i j=1 := by
    unfold quantizedCapKernel
    rw [capKernel_eq_ite]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  apply bernoulli_feature_square_le _ p (fun _ => ENNReal.toReal_nonneg)
    (gridLaw_mass_total σ) q _ ENNReal.toReal_nonneg bs _ i
  intro l
  simp_rw [show ∀ j, p j=σ.real (gridCode d m ⁻¹' {j}) from gridLaw_atom σ]
  exact quantized_row_upper n m mp t a l lo hi

#print axioms gridSample_preserving
#print axioms quantized_grid_feature_bound
end RobustFolkman.GeometricGap
